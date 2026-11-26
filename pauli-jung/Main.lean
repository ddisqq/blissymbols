import PauliJung

/-!
# `paulijung`: print the causal analysis of every case

Runs the verified checker of `PauliJung.Decide` on each case model and
prints, for the mental/physical pair in question, the two causal pasts and
the verdict. The verdicts printed here are the ones proved in
`PauliJung.Applications`.
-/

open PauliJung

def short (s : String) : String := (s.splitOn ".").getLast!

def showState {α β : Type} [Repr α] [Repr β] : Sum α β → String
  | .inl a => short (reprStr a)
  | .inr b => short (reprStr b)

def row {W : Model} [DecidableEq (Sum W.M W.P)] [Repr W.M] [Repr W.P]
    (name : String) (F : Presentation W) (m : W.M) (p : W.P) : String :=
  let x : Sum W.M W.P := .inl m
  let y : Sum W.M W.P := .inr p
  let past (z : Sum W.M W.P) := ", ".intercalate ((anc F.nodes F.edge z).map showState)
  let verdict :=
    if !certB F.nodes F.edge x y then "UNDECIDED (closure check failed)"
    else if linkedB F.nodes F.edge x y then "causally linked: not a synchronicity"
    else "no causal link: synchronicity if meaningful"
  s!"{name}\n  pair:           {showState x}  ~  {showState y}\n" ++
  s!"  mental past:    {past x}\n  physical past:  {past y}\n  verdict:        {verdict}\n"

def report : List String :=
  [ row "1. Scarab" scarabPres .recountsDream .beetleTaps,
    row "1b. Scarab, Jung as common observer" scarabColliderPres .recountsDream .beetleTaps,
    row "2. Pauli effect" pauliPres .pauliOnTrain .apparatusFails,
    row "3. Birds at the death" birdsPres .wifeAlarmed .husbandCollapses,
    row "4. Swedenborg's fire" swedPres .visionOfFire .fireSpreads,
    row "5a. Plum pudding, boyhood" puddingPres .tastesPudding .fontgibuGivesPudding,
    row "5b. Plum pudding, restaurant" puddingPres .ordersPudding .lastPuddingTaken,
    row "5c. Plum pudding, dinner" puddingPres .remarksAbsence .fontgibuEnters,
    row "6. April fish (single encounter)" fishPres .noticesFish .fishPresent,
    row "7a. Room 137, the physics" room137Pres .computesAlpha .spectrumMeasured,
    row "7b. Room 137, the room" room137Pres .preoccupiedWith137 .assignedRoom137,
    row "8. I Ching (strict reading)" ichingPres .asksAboutBook .hexagram50 ]

def main : IO Unit := do
  IO.println "Pauli–Jung synchronicity: causal analysis of the cases"
  IO.println "(cases 9 and 10, Rhine and astrology, are statistical; see PauliJung.Cases)\n"
  for r in report do IO.println r
