import PauliJung.Decide

/-!
# World files

A small text format for describing a dual-aspect world, and an analysis
that runs the same functions (`anc`, `linkedB`) that `PauliJung.Decide`
proves correct. States are names; the file is checked for undeclared names
before anything is computed.

```
# comment
mental    recountsDream jungNotices
physical  beetleFlies beetleTaps
cause     beetleFlies -> beetleTaps
cause     beetleTaps -> jungNotices
neutral   session : recountsDream / beetleTaps
archetype rebirth @ session : recountsDream / beetleTaps
check     recountsDream ~ beetleTaps
```

* `neutral u : m / p` — neutral state `u` has mental aspect `m`, physical `p`.
* `archetype a @ u… : m… / p…` — `a` is constellated in the listed neutral
  states and gives meaning to the listed mental and physical states.
* `check m ~ p` — analyse this pair. Without any `check`, every neutral
  state's aspect pair is analysed.
-/

namespace PauliJung.Script

structure Archetype where
  name : String
  neutrals : List String
  mental : List String
  physical : List String

structure World where
  mental : List String := []
  physical : List String := []
  causes : List (String × String) := []
  neutrals : List (String × String × String) := []
  archetypes : List Archetype := []
  checks : List (String × String) := []

/-- Words of a line, with any `#` comment removed. -/
def words (line : String) : List String :=
  let body := (line.splitOn "#").headD ""
  (body.splitToList (fun c => c == ' ' || c == '\t' || c == '\r')).filter (· ≠ "")

/-- Split a word list at the first occurrence of a separator. -/
def splitAt (sep : String) : List String → Option (List String × List String)
  | [] => none
  | w :: ws =>
    if w == sep then some ([], ws)
    else (splitAt sep ws).map fun (a, b) => (w :: a, b)

def parseLine (n : Nat) (w : World) (line : String) : Except String World :=
  let bad (msg : String) : Except String World := .error s!"line {n}: {msg}"
  match words line with
  | [] => .ok w
  | "mental" :: xs => .ok { w with mental := w.mental ++ xs }
  | "physical" :: xs => .ok { w with physical := w.physical ++ xs }
  | ["cause", a, "->", b] => .ok { w with causes := w.causes ++ [(a, b)] }
  | ["neutral", u, ":", m, "/", p] => .ok { w with neutrals := w.neutrals ++ [(u, m, p)] }
  | ["check", m, "~", p] => .ok { w with checks := w.checks ++ [(m, p)] }
  | "archetype" :: a :: "@" :: rest =>
    match splitAt ":" rest with
    | none => bad "expected `archetype NAME @ NEUTRALS : MENTAL / PHYSICAL`"
    | some (us, rest) =>
      match splitAt "/" rest with
      | none => bad "expected `/` between mental and physical states"
      | some (ms, ps) =>
        .ok { w with archetypes := w.archetypes ++ [⟨a, us, ms, ps⟩] }
  | kw :: _ => bad s!"cannot read this line (starts with `{kw}`)"

def parse (text : String) : Except String World := do
  let mut w : World := {}
  let mut n := 1
  for line in text.splitOn "\n" do
    w ← parseLine n w line
    n := n + 1
  return w

/-- Check that every name used is declared, and that no name is both mental
and physical. Returns the list of problems. -/
def validate (w : World) : List String :=
  let isM (x : String) := w.mental.contains x
  let isP (x : String) := w.physical.contains x
  let isState (x : String) := isM x || isP x
  let isU (x : String) := w.neutrals.any (·.1 == x)
  (w.mental.filter isP).map (fun x => s!"`{x}` is declared both mental and physical") ++
  (w.causes.flatMap fun (a, b) => [a, b]).filter (!isState ·)
    |>.map (fun x => s!"cause mentions undeclared state `{x}`") |>.append
  ((w.neutrals.filter fun (_, m, _) => !isM m).map
    fun (u, m, _) => s!"neutral `{u}`: `{m}` is not a mental state") |>.append
  ((w.neutrals.filter fun (_, _, p) => !isP p).map
    fun (u, _, p) => s!"neutral `{u}`: `{p}` is not a physical state") |>.append
  (w.archetypes.flatMap fun a =>
    (a.neutrals.filter (!isU ·)).map (fun x => s!"archetype `{a.name}`: unknown neutral state `{x}`") ++
    (a.mental.filter (!isM ·)).map (fun x => s!"archetype `{a.name}`: `{x}` is not a mental state") ++
    (a.physical.filter (!isP ·)).map (fun x => s!"archetype `{a.name}`: `{x}` is not a physical state")) |>.append
  ((w.checks.filter fun (m, _) => !isM m).map
    fun (m, _) => s!"check: `{m}` is not a mental state") |>.append
  ((w.checks.filter fun (_, p) => !isP p).map
    fun (_, p) => s!"check: `{p}` is not a physical state")

def World.nodes (w : World) : List String := w.mental ++ w.physical

def World.edge (w : World) (a b : String) : Bool := w.causes.contains (a, b)

/-- Archetypes that make the pair a meaningful coincidence. -/
def World.meanings (w : World) (m p : String) : List String :=
  (w.archetypes.filter fun a =>
    a.mental.contains m && a.physical.contains p &&
    w.neutrals.any fun (u, um, up) => a.neutrals.contains u && um == m && up == p).map (·.name)

def World.linked (w : World) (m p : String) : Bool := linkedB w.nodes w.edge m p

/-- The kind of causal link, for the report. -/
def World.linkKind (w : World) (m p : String) : String :=
  let pm := anc w.nodes w.edge m
  let pp := anc w.nodes w.edge p
  if pp.contains m then s!"{m} leads to {p}"
  else if pm.contains p then s!"{p} leads to {m}"
  else
    let common := pm.filter pp.contains
    s!"common cause: {", ".intercalate common}"

def World.report (w : World) (m p : String) : String :=
  let pm := anc w.nodes w.edge m
  let pp := anc w.nodes w.edge p
  let ms := w.meanings m p
  let linked := w.linked m p
  let verdict :=
    if !ms.isEmpty && !linked then "SYNCHRONICITY"
    else if !ms.isEmpty then "meaningful, but causally linked: not a synchronicity"
    else if linked then "causally linked, no shared meaning: not a synchronicity"
    else "no shared meaning: not a synchronicity"
  s!"{m}  ~  {p}\n" ++
  s!"  mental past:     {", ".intercalate pm}\n" ++
  s!"  physical past:   {", ".intercalate pp}\n" ++
  s!"  meaning:         {if ms.isEmpty then "none" else ", ".intercalate ms}\n" ++
  s!"  causal link:     {if linked then w.linkKind m p else "none"}\n" ++
  s!"  verdict:         {verdict}\n"

/-- Analyse a world file: either a list of problems or one report per pair. -/
def analyse (text : String) : Except (List String) (List String) :=
  match parse text with
  | .error e => .error [e]
  | .ok w =>
    match validate w with
    | [] =>
      let pairs := if w.checks.isEmpty then w.neutrals.map (fun (_, m, p) => (m, p)) else w.checks
      .ok (pairs.map fun (m, p) => w.report m p)
    | errs => .error errs

end PauliJung.Script
