import PauliJung.MoreCases
import Bliss.Verified

/-!
# The Pauli–Jung cases written in Blissymbols

Each case becomes a three-symbol sentence: the mental state, a link, and
the physical event, together with the archetype that gives them meaning.
The middle symbol is not chosen by hand: it is computed from the decision
procedure's verdict.

* *meaning* — the pair is a synchronicity;
* *cause* — the pair is causally linked;
* *chance* — neither linked nor meaningful.

`link_is_meaning_iff` states that the sentence says "meaning" exactly when
the pair is a synchronicity, and `vocabulary_exists` that every symbol used
is in the Blissymbol database.
-/

namespace PauliJung

open Bliss

/-- Blissymbol for "meaning". -/
def symMeaning : String := "meaning,sense,significance"
/-- Blissymbol for "cause". -/
def symCause : String := "cause"
/-- Blissymbol for "chance". -/
def symChance : String := "accident,chance_event"
/-- Blissymbol for the mental aspect. -/
def symMind : String := "mind,intellect,reason"
/-- Blissymbol for the physical aspect. -/
def symMatter : String := "earth,globe,world"

/-- The Blissymbol standing for each archetype. -/
def archSymbol : Arch → String
  | .rebirth => "birth"
  | .shadow => "shadow,shade"
  | .death => "death"
  | .fire => "fire"
  | .series => "repetition,copying,duplication,replication"
  | .fish => "fish_(animal)"
  | .number => "number"
  | .wholeness => "all,every,everything,total,whole"
  | .psi => "mind,intellect,reason"
  | .union => "marriage"
  | .animal => "animal,beast"

/-- The link symbol determined by a verdict. -/
def linkSymbol (sync linked : Bool) : String :=
  if sync then symMeaning else if linked then symCause else symChance

/-- A case written as a Blissymbol sentence. -/
structure Sentence where
  title : String
  mental : String
  link : String
  physical : String
  archetype : String
  sync : Bool
  meaningful : Bool
  linked : Bool

section
variable {W : Model} [DecidableEq W.M] [DecidableEq W.P]
  [∀ a u, Decidable (W.constellated a u)]
  [∀ a m, Decidable (W.expressesM a m)] [∀ a p, Decidable (W.expressesP a p)]

/-- Build the sentence of a pair from the decision procedure. -/
def mkSentence (F : FullPresentation W) (title : String) (m : W.M) (p : W.P)
    (mental physical archetype : String) : Sentence :=
  let linked := linkedB F.nodes F.edge (.inl m) (.inr p)
  { title, mental, physical, archetype
    link := linkSymbol (F.syncB m p) linked
    sync := F.syncB m p
    meaningful := F.meaningfulB m p
    linked }

theorem linkSymbol_eq_meaning (s l : Bool) : linkSymbol s l = symMeaning ↔ s = true := by
  cases s <;> cases l <;> decide

theorem linkSymbol_eq_cause (s l : Bool) :
    linkSymbol s l = symCause ↔ s = false ∧ l = true := by
  cases s <;> cases l <;> decide

/-- **The sentence says "meaning" exactly for synchronicities.** -/
theorem link_is_meaning_iff (F : FullPresentation W) (title : String) (m : W.M) (p : W.P)
    (mental physical archetype : String) :
    (mkSentence F title m p mental physical archetype).link = symMeaning ↔
      Synchronicity W m p := by
  show linkSymbol (F.syncB m p) _ = symMeaning ↔ _
  rw [linkSymbol_eq_meaning]
  exact (F.sync_iff_syncB m p).symm

/-- It says "cause" exactly when the pair is causally linked. -/
theorem link_is_cause_iff (F : FullPresentation W) (title : String) (m : W.M) (p : W.P)
    (mental physical archetype : String) :
    (mkSentence F title m p mental physical archetype).link = symCause ↔
      CausallyLinked W (.inl m) (.inr p) := by
  show linkSymbol (F.syncB m p) (linkedB F.nodes F.edge (.inl m) (.inr p)) = symCause ↔ _
  rw [linkSymbol_eq_cause, F.toPresentation.linked_iff']
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simp [FullPresentation.syncB, h], h⟩
end

/-- The cases as sentences. -/
def sentences : List Sentence :=
  [ mkSentence scarabColliderFull "The scarab" .recountsDream .beetleTaps
      "dream-(to)" "insect,bug" (archSymbol .rebirth),
    mkSentence pauliFull "The Pauli effect" .pauliOnTrain .apparatusFails
      "mind,intellect,reason" "machine,appliance,engine,motor" (archSymbol .shadow),
    mkSentence birdsFull "Birds at a death" .wifeAlarmed .husbandCollapses
      "fear,fright,concern" "death" (archSymbol .death),
    mkSentence swedFull "Swedenborg's fire" .visionOfFire .fireSpreads
      "vision,apparition" "fire" (archSymbol .fire),
    mkSentence puddingFull "The plum pudding" .remarksAbsence .fontgibuEnters
      "idea,thought" "pudding,cream" (archSymbol .series),
    mkSentence fishFull "The April fish" .noticesFish .fishPresent
      "sight,vision,visual_sense" "fish_(animal)" (archSymbol .fish),
    mkSentence room137Full "Room 137" .preoccupiedWith137 .assignedRoom137
      "number" "room" (archSymbol .number),
    mkSentence ichingFull "The I Ching" .asksAboutBook .hexagram50
      "question" "book" (archSymbol .wholeness),
    mkSentence foxFull "The fox in the wood" .tellsFoxDream .foxOnPath
      "dream-(to)" "fox,jackal,coyote" (archSymbol .animal),
    mkSentence clockFull "The stopped clock" .ownerDying .clockStops
      "death" "clock,timepiece" (archSymbol .death),
    mkSentence kammFull "Kammerer's series" .idleAttention .concertTicketNine
      "number" "ticket,pass" (archSymbol .series),
    mkSentence bookFull "The bookcase: first report" .feelsHeat .firstCrack
      "heat" "sound" (archSymbol .shadow),
    mkSentence bookFull "The bookcase: the prediction" .predictsSecond .secondCrack
      "idea,thought" "sound" (archSymbol .shadow) ]

/-- Is this the name of a character or a word of the database? -/
def symbolExists (s : String) : Bool :=
  chars.any (fun c => c.name == s) || words.any (fun w => w.1 == s)

/-- Every symbol used anywhere in the sentences. -/
def vocabulary : List String :=
  [symMeaning, symCause, symChance, symMind, symMatter] ++
  sentences.flatMap fun s => [s.mental, s.link, s.physical, s.archetype]

set_option maxRecDepth 100000 in
/-- **Every symbol used is a Blissymbol of the database.** -/
theorem vocabulary_exists : vocabulary.all symbolExists = true := by decide +kernel

end PauliJung
