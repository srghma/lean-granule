module

/-!
# Granule lexer

A hand-written port of the Alex lexer `Language.Granule.Syntax.Lexer`.
Alex semantics are reproduced: at each position the *longest* match among all
rules wins, and ties are broken in favour of the rule listed first.  In
particular newline tokens are only produced for whitespace runs that end in a
newline (so indented continuation lines do not produce a newline token), which
is how Granule's layout works.
-/

@[expose] public section

namespace Granule

inductive Tok where
  | nl
  | kw (s : String)          -- keywords: let in if then else data where module hiding case
                             -- spec of try as catch share clone endorse pack unpack exists
                             -- mut forall
  | import (path : String)
  | pragma
  | constr (s : String)
  | sym (s : String)
  | int (n : Int)
  | float (s : String)
  | char (c : Char)
  | string (s : String)
  | op (s : String)          -- punctuation and operators, normalised to ASCII spelling
  deriving Repr, BEq, Inhabited

structure Token where
  tok : Tok
  line : Nat
  col : Nat
  deriving Repr, Inhabited

namespace Lexer

def isWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == '\x0b'

def isAlpha (c : Char) : Bool := c.isAlpha || c == '_' || c == '-' || c == '='
def isAlphaNum (c : Char) : Bool := isAlpha c || c.isDigit
def isFruit (c : Char) : Bool := c.toNat ≥ 127815 && c.toNat ≤ 127827

/-- Length of the longest prefix satisfying `p`. -/
def spanLen (p : Char → Bool) : List Char → Nat
  | c :: cs => if p c then spanLen p cs + 1 else 0
  | [] => 0

/-- `$white* $eol`: longest whitespace prefix ending in a newline. -/
def matchWhiteEol (cs : List Char) : Option Nat :=
  let rec go (cs : List Char) (i : Nat) (best : Option Nat) : Option Nat :=
    match cs with
    | c :: rest => if isWhite c then go rest (i + 1) (if c == '\n' then some (i + 1) else best)
                   else best
    | [] => best
  go cs 0 none

def matchWhite (cs : List Char) : Option Nat :=
  let n := spanLen isWhite cs
  if n > 0 then some n else none

def matchLineComment : List Char → Option Nat
  | '-' :: '-' :: rest => some (2 + spanLen (· != '\n') rest)
  | _ => none

/-- `"{-" (\\.|[^\{\-]|\n)* "-}"` -/
def matchBlockComment : List Char → Option Nat
  | '{' :: '-' :: rest =>
    let rec go : List Char → Nat → Option Nat
      | '-' :: '}' :: _, i => some (i + 2)
      | '\\' :: _ :: cs, i => go cs (i + 2)
      | c :: cs, i => if c == '{' || c == '-' then none else go cs (i + 1)
      | [], _ => none
    go rest 2
  | _ => none

def matchPrefix (s : String) (cs : List Char) : Option Nat :=
  if s.toList.isPrefixOf cs then some s.length else none

/-- `import $white+ @importFilePath` -/
def matchImport (cs : List Char) : Option Nat :=
  match matchPrefix "import" cs with
  | some 6 =>
    let rest := cs.drop 6
    let w := spanLen isWhite rest
    if w == 0 then none
    else some (6 + w + spanLen (fun c => isAlphaNum c || c == '\'' || c == '.') (rest.drop w))
  | _ => none

/-- `language $white+` -/
def matchPragma (cs : List Char) : Option Nat :=
  match matchPrefix "language" cs with
  | some 8 =>
    let w := spanLen isWhite (cs.drop 8)
    if w == 0 then none else some (8 + w)
  | _ => none

/-- `@constr = $upper ($alphanum | ')* | ()` -/
def matchConstr : List Char → Option Nat
  | '(' :: ')' :: _ => some 2
  | c :: cs => if c.isUpper then some (1 + spanLen (fun c => isAlphaNum c || c == '\'') cs) else none
  | [] => none

/-- `@sym = $lower ($alphanum | ')* | $fruit` -/
def matchSym : List Char → Option Nat
  | c :: cs =>
    if c.isLower then some (1 + spanLen (fun c => isAlphaNum c || c == '\'') cs)
    else if isFruit c then some 1 else none
  | [] => none

/-- `@int = -? $digit+` -/
def matchInt (cs : List Char) : Option Nat :=
  let (sign, rest) := match cs with
    | '-' :: r => (1, r)
    | r => (0, r)
  let d := spanLen Char.isDigit rest
  if d == 0 then none else some (sign + d)

/-- `@float = -? $digit+ \. $digit+` -/
def matchFloat (cs : List Char) : Option Nat := do
  let n ← matchInt cs
  match cs.drop n with
  | '.' :: rest =>
    let d := spanLen Char.isDigit rest
    if d == 0 then none else some (n + 1 + d)
  | _ => none

/-- `@charLiteral = \' (\\.|[^\']| . ) \'` -/
def matchChar : List Char → Option Nat
  | '\'' :: '\\' :: _ :: '\'' :: _ => some 4
  | '\'' :: _ :: '\'' :: _ => some 3
  | _ => none

/-- `@stringLiteral = \"(\\.|[^\"]|\n)*\"` -/
def matchString : List Char → Option Nat
  | '"' :: rest =>
    let rec go : List Char → Nat → Option Nat
      | '"' :: _, i => some (i + 1)
      | '\\' :: _ :: cs, i => go cs (i + 2)
      | _ :: cs, i => go cs (i + 1)
      | [], _ => none
    go rest 1
  | _ => none

/-- Keywords, in rule order. -/
def keywords : List (String × String) :=
  [("forall", "forall"), ("∀", "forall"), ("let", "let"), ("data", "data"), ("where", "where"),
   ("module", "module"), ("hiding", "hiding"), ("in", "in"), ("if", "if"), ("then", "then"),
   ("else", "else"), ("case", "case"), ("spec", "spec"), ("of", "of"), ("try", "try"),
   ("as", "as"), ("catch", "catch"), ("share", "share"), ("clone", "clone"),
   ("endorse", "endorse"), ("pack", "pack"), ("unpack", "unpack"), ("exists", "exists"),
   ("mut", "mut"), ("∃", "exists")]

/-- Operators and punctuation, in rule order, with their normalised name. -/
def operators : List (String × String) :=
  [("@", "@"), ("->", "->"), ("→", "->"), ("<-", "<-"), ("←", "<-"), (";", ";"), ("=", "="),
   ("/=", "/="), ("≠", "/="), ("\\", "\\"), ("λ", "\\"), ("[", "["), ("]", "]"), ("+", "+"),
   ("-", "-"), ("*", "*"), ("(", "("), (")", ")"), ("{", "{"), ("}", "}"), ("<", "<"),
   (">", ">"), (",", ","), ("×", "×"), (".", "."), (":", ":")]

/-- Operators listed after `@sym` in the Alex file. -/
def operators2 : List (String × String) :=
  [("_", "_"), ("|", "|"), ("/", "/"), ("≤", "<="), ("<=", "<="), ("≥", ">="), (">=", ">="),
   ("==", "=="), ("≡", "=="), ("`", "`"), ("^", "^"), ("..", ".."), ("∨", "\\/"),
   ("\\/", "\\/"), ("∧", "/\\"), ("/\\", "/\\"), ("=>", "=>"), ("⇒", "=>"), ("∘", "∘"),
   ("?", "?"), ("{!", "{!"), ("!}", "!}"), ("!", "!"), ("&", "&"), ("#", "#"), ("⊸", "->"),
   ("*{", "*{"), ("%", "%"), ("⨱", "⨱")]

/-- Read a Haskell character escape sequence (after the backslash).
Returns the character and the remaining input. -/
def readEscape : List Char → Option (Char × List Char)
  | 'n' :: r => some ('\n', r)
  | 't' :: r => some ('\t', r)
  | 'r' :: r => some ('\r', r)
  | '\\' :: r => some ('\\', r)
  | '\'' :: r => some ('\'', r)
  | '"' :: r => some ('"', r)
  | '0' :: r => some ('\x00', r)
  | 'a' :: r => some ('\x07', r)
  | 'b' :: r => some ('\x08', r)
  | 'f' :: r => some ('\x0c', r)
  | 'v' :: r => some ('\x0b', r)
  | cs@(c :: _) =>
    if c.isDigit then
      let ds := cs.takeWhile Char.isDigit
      let n := ds.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
      some (Char.ofNat n, cs.drop ds.length)
    else none
  | [] => none

/-- Haskell `read` of a string literal body (without quotes). -/
partial def readStringBody : List Char → String
  | [] => ""
  | '\\' :: '&' :: r => readStringBody r
  | '\\' :: r =>
    match readEscape r with
    | some (c, r') => String.singleton c ++ readStringBody r'
    | none => "\\" ++ readStringBody r
  | c :: r => String.singleton c ++ readStringBody r

/-- One lexing step result. -/
inductive Step where
  | skip
  | emit (t : Tok)

/-- All rules in order, each giving the match length and the token builder. -/
def charTok (s : String) : Option Step :=
  match s.toList with
  | ['\'', '\\', c, '\''] => (readEscape [c]).map fun p => Step.emit (Tok.char p.1)
  | ['\'', c, '\''] => some (.emit (.char c))
  | _ => none

def emitK (t : Tok) : String → Option Step := fun _ => some (.emit t)

def rules (cs : List Char) : List (Option Nat × (String → Option Step)) :=
  let mk (f : String → Tok) (p : String × String) : Option Nat × (String → Option Step) :=
    (matchPrefix p.1 cs, emitK (f p.2))
  let kw := keywords.map (mk Tok.kw)
  let ops := operators.map (mk Tok.op)
  let ops2 := operators2.map (mk Tok.op)
  let r (m : Option Nat) (f : String → Option Step) : Option Nat × (String → Option Step) := (m, f)
  [ r (matchWhiteEol cs) (emitK .nl),
    r (if cs.headD ' ' == '\n' then some (spanLen (· == '\n') cs) else none) (emitK .nl),
    r (matchWhite cs) (fun _ => some .skip),
    r (matchLineComment cs) (fun _ => some .skip),
    r (matchBlockComment cs) (fun _ => some .skip),
    r (matchImport cs) (fun s => some (.emit (.import s))),
    r (matchPragma cs) (emitK .pragma),
    r (matchConstr cs) (fun s => some (.emit (.constr s))) ] ++
  kw ++
  [ r (matchPrefix "∞" cs) (emitK (.op "∞")),
    r (matchFloat cs) (fun s => some (.emit (.float s))),
    r (matchInt cs) (fun s => some (.emit (.int s.toInt!))),
    r (matchChar cs) charTok,
    r (matchString cs) (fun s =>
      some (.emit (.string (readStringBody ((s.toList.drop 1).dropLast))))) ] ++
  ops ++
  [ r (matchSym cs) (fun s => some (.emit (.sym s))) ] ++
  ops2

/-- Pick the longest match, earliest rule on ties. -/
def bestRule (cs : List Char) : Option (Nat × (String → Option Step)) :=
  (rules cs).foldl (fun best (m, f) =>
    match m, best with
    | some n, none => if n > 0 then some (n, f) else none
    | some n, some (b, g) => if n > b then some (n, f) else some (b, g)
    | none, best => best) none

/-- Advance a (line, column) position over some characters. -/
def advance (pos : Nat × Nat) (cs : List Char) : Nat × Nat :=
  cs.foldl (fun (l, c) ch => if ch == '\n' then (l + 1, 1) else (l, c + 1)) pos

partial def scanAux (cs : List Char) (pos : Nat × Nat) (acc : Array Token) :
    Except String (Array Token) :=
  match cs with
  | [] => .ok acc
  | _ =>
    match bestRule cs with
    | none => .error s!"{pos.1}:{pos.2}: lexical error"
    | some (n, f) =>
      let lexeme := cs.take n
      let pos' := advance pos lexeme
      match f (String.ofList lexeme) with
      | none => .error s!"{pos.1}:{pos.2}: lexical error"
      | some .skip => scanAux (cs.drop n) pos' acc
      | some (.emit t) => scanAux (cs.drop n) pos' (acc.push ⟨t, pos.1, pos.2⟩)

end Lexer

/-- Tokenise a source string; leading and trailing newline tokens are trimmed
(as `scanTokens` does in the Haskell lexer). -/
def scanTokens (s : String) : Except String (List Token) := do
  let ts ← Lexer.scanAux s.toList (1, 1) #[]
  let ts := ts.toList.dropWhile (·.tok == .nl)
  return (ts.reverse.dropWhile (·.tok == .nl)).reverse

end Granule

end
