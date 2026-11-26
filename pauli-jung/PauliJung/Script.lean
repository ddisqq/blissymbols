import PauliJung.Decide

/-!
# World files

A small text format for describing a dual-aspect world. A file is checked
for undeclared names, compiled to a genuine `Model` with a finite
presentation, and analysed by the decision procedure of `PauliJung.Decide`;
`CWorld.verdict_correct` states that the printed verdict is right for the
model the file describes.

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

/-! ### Compiling a world file to a model

Names become indices, so the world becomes a genuine `Model` with a
`FullPresentation`. The verdict printed is then literally the value of the
decision procedure, and `verdict_correct` applies to it. -/

/-- A world with states as indices. -/
structure CWorld where
  nM : Nat
  nP : Nat
  /-- Causal edges, on coded states. -/
  edges : List (Sum Nat Nat × Sum Nat Nat)
  /-- Neutral states, as (mental aspect, physical aspect). -/
  ns : List (Fin nM × Fin nP)
  /-- Archetypes, as (neutral states, mental states, physical states). -/
  as : List (List Nat × List Nat × List Nat)

/-- Code a manifest state as a tagged number. -/
def code {m n : Nat} : Sum (Fin m) (Fin n) → Sum Nat Nat
  | .inl i => .inl i.val
  | .inr j => .inr j.val

/-- The model described by a compiled world. -/
@[reducible] def CWorld.toModel (C : CWorld) : Model where
  U := Fin C.ns.length
  M := Fin C.nM
  P := Fin C.nP
  A := Fin C.as.length
  ψ := fun u => (C.ns.get u).1
  φ := fun u => (C.ns.get u).2
  causes := fun x y => C.edges.contains (code x, code y) = true
  constellated := fun a u => (C.as.get a).1.contains u.val = true
  expressesM := fun a m => (C.as.get a).2.1.contains m.val = true
  expressesP := fun a p => (C.as.get a).2.2.contains p.val = true

/-- Its finite presentation. -/
def CWorld.full (C : CWorld) : FullPresentation C.toModel where
  nodes := (List.finRange C.nM).map Sum.inl ++ (List.finRange C.nP).map Sum.inr
  edge := fun x y => C.edges.contains (code x, code y)
  complete := by intro x; cases x <;> simp
  faithful := fun _ _ => Iff.rfl
  neutrals := List.finRange _
  archetypes := List.finRange _
  neutrals_complete := by intro u; simp
  archetypes_complete := by intro a; simp

/-- **What the program prints is correct**: for the model described by the
file, the computed verdict is true exactly when the pair is a synchronicity. -/
theorem CWorld.verdict_correct (C : CWorld) (m : Fin C.nM) (p : Fin C.nP) :
    Synchronicity C.toModel m p ↔ C.full.syncB m p = true :=
  C.full.sync_iff_syncB m p

/-- Compile a (validated) world. Names that cannot be resolved are dropped;
`validate` guarantees there are none. -/
def compile (w : World) : CWorld :=
  let st (x : String) : Option (Sum Nat Nat) :=
    match w.mental.idxOf? x with
    | some i => some (.inl i)
    | none => (w.physical.idxOf? x).map .inr
  let unames := w.neutrals.map (·.1)
  { nM := w.mental.length
    nP := w.physical.length
    edges := w.causes.filterMap fun (a, b) =>
      match st a, st b with
      | some x, some y => some (x, y)
      | _, _ => none
    ns := w.neutrals.filterMap fun (_, m, p) =>
      match w.mental.finIdxOf? m, w.physical.finIdxOf? p with
      | some i, some j => some (i, j)
      | _, _ => none
    as := w.archetypes.map fun a =>
      (a.neutrals.filterMap unames.idxOf?, a.mental.filterMap w.mental.idxOf?,
       a.physical.filterMap w.physical.idxOf?) }

def World.stateName (w : World) : Sum (Fin (compile w).nM) (Fin (compile w).nP) → String
  | .inl i => w.mental.getD i.val "?"
  | .inr j => w.physical.getD j.val "?"

def World.report (w : World) (m : Fin (compile w).nM) (p : Fin (compile w).nP) : String :=
  let C := compile w
  let F := C.full
  let x : Sum (Fin C.nM) (Fin C.nP) := .inl m
  let y : Sum (Fin C.nM) (Fin C.nP) := .inr p
  let pm := anc F.nodes F.edge x
  let pp := anc F.nodes F.edge y
  let names (l : List (Sum (Fin C.nM) (Fin C.nP))) := ", ".intercalate (l.map w.stateName)
  let ms := (List.finRange C.as.length).filter fun a =>
    (List.finRange C.ns.length).any fun u =>
      decide (C.toModel.constellated a u ∧ C.toModel.ψ u = m ∧ C.toModel.φ u = p ∧
        C.toModel.expressesM a m ∧ C.toModel.expressesP a p)
  let meaning := ", ".intercalate (ms.map fun a => (w.archetypes.map (·.name)).getD a.val "?")
  let linked := linkedB F.nodes F.edge x y
  let link :=
    if !linked then "none"
    else if pp.contains x then s!"{w.stateName x} leads to {w.stateName y}"
    else if pm.contains y then s!"{w.stateName y} leads to {w.stateName x}"
    else s!"common cause: {names (pm.filter pp.contains)}"
  let verdict :=
    if F.syncB m p then "SYNCHRONICITY"
    else if F.meaningfulB m p then "meaningful, but causally linked: not a synchronicity"
    else if linked then "causally linked, no shared meaning: not a synchronicity"
    else "no shared meaning: not a synchronicity"
  s!"{w.stateName x}  ~  {w.stateName y}\n" ++
  s!"  mental past:     {names pm}\n" ++
  s!"  physical past:   {names pp}\n" ++
  s!"  meaning:         {if ms.isEmpty then "none" else meaning}\n" ++
  s!"  causal link:     {link}\n" ++
  s!"  verdict:         {verdict}\n"

/-- Analyse a world file: either a list of problems or one report per pair. -/
def analyse (text : String) : Except (List String) (List String) :=
  match parse text with
  | .error e => .error [e]
  | .ok w =>
    match validate w with
    | [] =>
      let C := compile w
      let pairs : List (Fin C.nM × Fin C.nP) :=
        if w.checks.isEmpty then C.ns
        else w.checks.filterMap fun (m, p) =>
          match w.mental.finIdxOf? m, w.physical.finIdxOf? p with
          | some i, some j => some (i, j)
          | _, _ => none
      .ok (pairs.map fun (m, p) => w.report m p)
    | errs => .error errs

end PauliJung.Script
