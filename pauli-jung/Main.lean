import PauliJung

/-!
# `paulijung`: print the causal analysis of every case

Runs the verified checker of `PauliJung.Decide` on each case model and
prints, for the mental/physical pair in question, the two causal pasts,
whether the pair is meaningful, and the verdict. The procedure is proved
correct (`FullPresentation.sync_iff_syncB`), and the verdicts printed here
are the ones in `scorecard_decided`.
-/

open PauliJung

def short (s : String) : String := (s.splitOn ".").getLast!

def showState {α β : Type} [Repr α] [Repr β] : Sum α β → String
  | .inl a => short (reprStr a)
  | .inr b => short (reprStr b)

def row {W : Model} [DecidableEq W.M] [DecidableEq W.P] [Repr W.M] [Repr W.P]
    [∀ a u, Decidable (W.constellated a u)]
    [∀ a m, Decidable (W.expressesM a m)] [∀ a p, Decidable (W.expressesP a p)]
    (name : String) (F : FullPresentation W) (m : W.M) (p : W.P) : String :=
  let x : Sum W.M W.P := .inl m
  let y : Sum W.M W.P := .inr p
  let past (z : Sum W.M W.P) := ", ".intercalate ((anc F.nodes F.edge z).map showState)
  let meaningful := F.meaningfulB m p
  let linked := linkedB F.nodes F.edge x y
  let verdict :=
    if F.syncB m p then "SYNCHRONICITY"
    else if meaningful then "meaningful, but causally linked: not a synchronicity"
    else if linked then "causally linked, no shared meaning: not a synchronicity"
    else "no shared meaning: not a synchronicity"
  s!"{name}\n  pair:           {showState x}  ~  {showState y}\n" ++
  s!"  mental past:    {past x}\n  physical past:  {past y}\n" ++
  s!"  meaningful:     {meaningful}\n  causally linked: {linked}\n  verdict:        {verdict}\n"

def report : List String :=
  [ row "1. Scarab" scarabFull .recountsDream .beetleTaps,
    row "1b. Scarab, Jung as common observer" scarabColliderFull .recountsDream .beetleTaps,
    row "1c. Scarab, the dream before the session" scarabFull .dreamsOfScarab .still,
    row "2. Pauli effect" pauliFull .pauliOnTrain .apparatusFails,
    row "3. Birds at the death" birdsFull .wifeAlarmed .husbandCollapses,
    row "4. Swedenborg's fire" swedFull .visionOfFire .fireSpreads,
    row "5a. Plum pudding, boyhood" puddingFull .tastesPudding .fontgibuGivesPudding,
    row "5b. Plum pudding, restaurant" puddingFull .ordersPudding .lastPuddingTaken,
    row "5c. Plum pudding, dinner" puddingFull .remarksAbsence .fontgibuEnters,
    row "6. April fish (single encounter)" fishFull .noticesFish .fishPresent,
    row "7a. Room 137, the physics" room137Full .computesAlpha .spectrumMeasured,
    row "7b. Room 137, the room" room137Full .preoccupiedWith137 .assignedRoom137,
    row "8. I Ching (strict reading)" ichingFull .asksAboutBook .hexagram50 ]

def main : IO Unit := do
  IO.println "Pauli–Jung synchronicity: causal analysis of the cases"
  IO.println "(cases 9 and 10, Rhine and astrology, are statistical; see PauliJung.Cases)\n"
  for r in report do IO.println r
