module

public import RequestProject.Granule.Core

/-!
# Pretty printing of terms and values

A port of the `Pretty` instances for `Value` and `Expr` from
`Language.Granule.Syntax.Pretty`, together with ports of the Haskell `show`
functions for `Double`, `Char` and `String`/`Text` that it relies on.
-/

@[expose] public section

namespace Granule

namespace HaskellShow

/-- ASCII control character names as used by Haskell's `showLitChar`. -/
def asciiTab : Array String :=
  #["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF", "VT", "FF", "CR",
    "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM", "SUB",
    "ESC", "FS", "GS", "RS", "US", "SP"]

/-- `showLitChar c` followed by the next character (needed for `\&` protection). -/
def showLitChar (c : Char) (next : Option Char) : String :=
  let protect (p : Char → Bool) (s : String) : String :=
    match next with
    | some d => if p d then s ++ "\\&" else s
    | none => s
  let n := c.toNat
  if n > 127 then protect Char.isDigit ("\\" ++ toString n)
  else if n == 127 then "\\DEL"
  else if c == '\\' then "\\\\"
  else if n ≥ 32 then String.singleton c
  else if c == '\x07' then "\\a"
  else if c == '\x08' then "\\b"
  else if c == '\x0c' then "\\f"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c == '\x0b' then "\\v"
  else if n == 14 then protect (· == 'H') "\\SO"
  else "\\" ++ asciiTab[n]!

/-- Haskell `show` on a `Char`. -/
def showChar (c : Char) : String :=
  if c == '\'' then "'\\''" else "'" ++ showLitChar c none ++ "'"

/-- Haskell `show` on a `String` (or `Text`). -/
def showString (s : String) : String :=
  let rec go : List Char → String
    | [] => ""
    | c :: cs =>
      (if c == '"' then "\\\"" else showLitChar c cs.head?) ++ go cs
  "\"" ++ go s.toList ++ "\""

/-- Exact decomposition of a finite positive float as `m * 2^e`. -/
def floatParts (x : Float) : Nat × Int :=
  let (fr, e) := x.frExp   -- x = fr * 2^e with fr ∈ [0.5, 1)
  let m := (fr.scaleB 53).toUInt64.toNat
  (m, e - 53)

/-- Number of decimal digits of a positive natural number. -/
def numDigits (n : Nat) : Nat := (toString n).length

/-- Round `num / den` to the nearest natural number (ties to even). -/
def roundDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 == 0 then q else q + 1

/-- Shortest decimal digits `ds` and exponent `e` such that `x = 0.ds × 10^e`
round-trips (GHC's `floatToDigits 10`), for finite positive `x`. -/
def floatToDigits (x : Float) : List Nat × Int := Id.run do
  let (m, e2) := floatParts x
  -- x = num / den exactly
  let (num, den) : Nat × Nat :=
    if e2 ≥ 0 then (m * 2 ^ e2.toNat, 1) else (m, 2 ^ (-e2).toNat)
  -- decimal exponent E with 10^(E-1) ≤ x < 10^E
  let ipart := num / den
  let mut bigE : Int := 0
  if ipart > 0 then
    bigE := numDigits ipart
  else
    -- x < 1: find the number of leading zeros after the decimal point
    let mut k : Nat := 0
    while num * 10 ^ (k + 1) < den do
      k := k + 1
    bigE := -(k : Int)
  for p in [1:18] do
    -- scaled = round(x * 10^(p - E))
    let shift : Int := p - bigE
    let scaled :=
      if shift ≥ 0 then roundDiv (num * 10 ^ shift.toNat) den
      else roundDiv num (den * 10 ^ (-shift).toNat)
    -- rounding may carry into an extra digit
    let (scaled, bigE') :=
      if numDigits scaled > p then (scaled / 10, bigE + 1) else (scaled, bigE)
    -- candidate = scaled * 10^(E' - p)
    let ex : Int := bigE' - p
    let cand : Float :=
      if ex ≥ 0 then Float.ofScientific (scaled * 10 ^ ex.toNat) false 0
      else Float.ofScientific scaled true (-ex).toNat
    if cand == x then
      let ds := (toString scaled).toList.map (fun c => c.toNat - '0'.toNat)
      -- drop trailing zeros
      let ds := (ds.reverse.dropWhile (· == 0)).reverse
      return (if ds.isEmpty then [0] else ds, bigE')
  return ([0], 0)

/-- Haskell `show` on a `Double`. -/
def showDouble (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > 0 then "Infinity" else "-Infinity")
  else if x == 0 then (if 1 / x < 0 then "-0.0" else "0.0")
  else
    let neg := x < 0
    let ax := if neg then -x else x
    let (ds, e) := floatToDigits ax
    let digits := String.join (ds.map toString)
    let body :=
      if 0 < e && e ≤ 7 then
        -- fixed notation, 0.1 ≤ x < 10^7
        let en := e.toNat
        let intPart := String.join ((ds.take en).map toString) ++
          String.ofList (List.replicate (en - ds.length) '0')
        let fracDs := ds.drop en
        intPart ++ "." ++ (if fracDs.isEmpty then "0" else String.join (fracDs.map toString))
      else if e == 0 then
        "0." ++ digits
      else
        -- scientific notation d.ddde<n>
        let first := toString (ds.headD 0)
        let rest := ds.drop 1
        first ++ "." ++ (if rest.isEmpty then "0" else String.join (rest.map toString)) ++
          "e" ++ toString (e - 1)
    if neg then "-" ++ body else body

end HaskellShow

open HaskellShow

/-- Whether a term is printed without parentheses when nested
(`isLexicallyAtomic` for values and expressions). -/
def Term.isAtomic {n : Nat} : Term n → Bool
  | .closed v => v.isAtomic
  | .lam _ _ => false
  | .constr c ts => ts.toList.isEmpty || c == ","
  | .app (.app (.constr "," .nil) _) _ => true
  | .app (.app (.closed (.constr "," .nil)) _) _ => true
  | .app _ _ | .appTy _ _ | .binop _ _ _ | .letDiamond _ _ _ | .tryCatch _ _ _ _ | .case _ _
  | .unpack _ _ _ _ | .hole => false
  | _ => true

mutual

/-- Pretty printing of patterns. -/
def Pat.pretty {k : Nat} : Pat k → String
  | .var x => Ty.prettyId x
  | .wild => "_"
  | .box p => "[" ++ p.prettyNested ++ "]"
  | .int n => toString n
  | .float f => showDouble f
  | .char c => showChar c
  | .constr "," ps => "(" ++ ", ".intercalate (Pats.prettyList ps) ++ ")"
  | .constr c ps => " ".intercalate (Ty.prettyId c :: Pats.prettyList ps)

def Pat.prettyNested {k : Nat} : Pat k → String
  | .constr c ps =>
    if c == "," || Pats.prettyList ps == [] then Pat.pretty (.constr c ps)
    else "(" ++ Pat.pretty (.constr c ps) ++ ")"
  | p => p.pretty

def Pats.prettyList {k : Nat} : Pats k → List String
  | .nil => []
  | .cons p ps => p.prettyNested :: Pats.prettyList ps

end

mutual

/-- Names of the variables bound by a pattern, left to right. -/
def Pat.names {k : Nat} : Pat k → Vector String k
  | .var x => #v[x]
  | .wild | .int _ | .float _ | .char _ => #v[]
  | .box p => p.names
  | .constr _ ps => ps.names

def Pats.names {k : Nat} : Pats k → Vector String k
  | .nil => #v[]
  | .cons p ps => p.names ++ ps.names

end

/-- Pretty printing of terms (a port of `Pretty Value` and `Pretty Expr`).
`names` gives the source names of the free variables. -/
partial def Term.prettyIn {n : Nat} (names : Vector String n) : Term n → String
  | .var i => Ty.prettyId names[i]
  | .closed v => v.prettyIn #v[]
  | .global x => Ty.prettyId x
  | .app (.app (.constr "," .nil) t1) t2 =>
    "(" ++ t1.prettyIn names ++ ", " ++ t2.prettyIn names ++ ")"
  | .app (.lam p e1) e2 =>
    "let " ++ p.pretty ++ " = " ++ e2.prettyIn names ++ " in " ++ e1.prettyIn (names ++ p.names)
  | .app e1 e2 => nested names e1 ++ " " ++ nested names e2
  | .appTy e t => nested names e ++ " @ " ++ Ty.pretty.nested t
  | .binop o e1 e2 => e1.prettyIn names ++ " " ++ o.pretty ++ " " ++ e2.prettyIn names
  | .letDiamond p e1 e2 =>
    "let " ++ p.pretty ++ " :unknown <- " ++ e1.prettyIn names ++ " in " ++
      e2.prettyIn (names ++ p.names)
  | .tryCatch e1 p e2 e3 =>
    "try " ++ e1.prettyIn names ++ " as [" ++ p.pretty ++ "]  in " ++
      e2.prettyIn (names ++ p.names) ++ " catch " ++ e3.prettyIn names
  | .case e arms =>
    "\n    (case " ++ e.prettyIn names ++ " of\n      " ++
      ";\n      ".intercalate (prettyArms names arms) ++ ")"
  | .unpack a x e1 e2 =>
    "unpack <" ++ a ++ ", " ++ x ++ "> = " ++ e1.prettyIn names ++ " in " ++
      e2.prettyIn (names.push x)
  | .hole => "?"
  | .lam p e => "\\" ++ p.pretty ++ " -> " ++ e.prettyIn (names ++ p.names)
  | .promote e => "[" ++ e.prettyIn names ++ "]"
  | .pure e => "<" ++ e.prettyIn names ++ ">"
  | .nec e => "*" ++ e.prettyIn names
  | .ref e => "&" ++ e.prettyIn names
  | .constr c ts =>
    let args := ts.toList
    if c == "," then "(" ++ ", ".intercalate (args.map (·.prettyIn names)) ++ ")"
    else if args.isEmpty then Ty.prettyId c
    else " ".intercalate (Ty.prettyId c :: args.map (nested names))
  | .int i => toString i
  | .float f => showDouble f
  | .char c => showChar c
  | .string s => showString s
  | .pack t e x k t' =>
    "pack <" ++ t.pretty ++ ", " ++ e.prettyIn names ++ "> as exists {" ++ x ++ " : " ++
      k.pretty ++ "} . " ++ t'.pretty
  | .tyAbs (.inl (v, k)) e => "/\\(" ++ v ++ " : " ++ k.pretty ++ ") -> " ++ e.prettyIn names
  | .tyAbs (.inr ids) _ => "/\\{" ++ ", ".intercalate ids ++ "}"
  | .prim _ _ => "Some primitive"
  | .rt _ => "<runtime resource>"
  | .effect _ _ => "<suspended IO>"
  | .freeImpure e => "Impure(" ++ e.prettyIn names ++ ")"
  | .freeBind v _ _ => "do {... <- " ++ v.prettyIn names ++ "; ...}"
where
  nested {n : Nat} (names : Vector String n) (t : Term n) : String :=
    if t.isAtomic then t.prettyIn names else "(" ++ t.prettyIn names ++ ")"
  prettyArms {n : Nat} (names : Vector String n) : Arms n → List String
    | .nil => []
    | .cons p b rest =>
      (p.pretty ++ " -> " ++ b.prettyIn (names ++ p.names)) :: prettyArms names rest

/-- Pretty printing of closed terms (values). -/
def Term.pretty (t : Term 0) : String := t.prettyIn #v[]

end Granule

end
