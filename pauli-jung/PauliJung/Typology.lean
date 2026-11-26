import PauliJung.Cases

/-!
# Jung's three kinds of synchronicity

Jung sorted synchronicities by how the mental state stands to the physical
event in space and time:

1. the event coincides with the state, in the observer's presence;
2. the event is simultaneous but distant, and only verified afterwards;
3. the event lies in the future.

Here manifest states get a time and a place. In a world whose causes run
forward in time, a precognitive synchronicity cannot be retrocausation.
-/

namespace PauliJung

/-- Times and places for the manifest states of a world. -/
structure Staging (W : Model) where
  time : Sum W.M W.P → Nat
  place : Sum W.M W.P → Nat

/-- Jung's three kinds. -/
inductive Kind
  | coincident | distant | precognitive
  deriving DecidableEq, Repr

variable {W : Model} (S : Staging W)

/-- Causes never run backward in time. -/
def Chronological : Prop := ∀ x y, W.causes x y → S.time x ≤ S.time y

/-- The kind of a mental/physical pair. -/
def Staging.kind (m : W.M) (p : W.P) : Kind :=
  if S.time (.inl m) < S.time (.inr p) then .precognitive
  else if S.place (.inl m) = S.place (.inr p) then .coincident
  else .distant

/-- **No retrocausation.** In a chronological world a later physical event
has no causal path to an earlier mental state. -/
theorem no_retrocausation (hS : Chronological S) {m : W.M} {p : W.P}
    (h : S.time (.inl m) < S.time (.inr p)) :
    ¬ Path W.causes (.inr p) (.inl m) :=
  fun hp => Nat.not_le_of_gt h (Path.le S.time hS hp)

/-- For an anticipating mental state, the only causal explanations left are
that it brought the event about or that both have a common cause. -/
theorem anticipation_link_iff (hS : Chronological S) {m : W.M} {p : W.P}
    (h : S.time (.inl m) < S.time (.inr p)) :
    CausallyLinked W (.inl m) (.inr p) ↔
      Controls W m p ∨ ∃ z, Path W.causes z (.inl m) ∧ Path W.causes z (.inr p) := by
  constructor
  · rintro (hl | hl | hl)
    · exact Or.inl hl
    · exact absurd hl (no_retrocausation S hS h)
    · exact Or.inr hl
  · rintro (hl | hl)
    · exact Or.inl hl
    · exact Or.inr (Or.inr hl)

/-- A common cause is never later than either of its effects. -/
theorem common_cause_earlier (hS : Chronological S) {z x y : Sum W.M W.P}
    (hx : Path W.causes z x) (hy : Path W.causes z y) :
    S.time z ≤ S.time x ∧ S.time z ≤ S.time y :=
  ⟨Path.le S.time hS hx, Path.le S.time hS hy⟩

/-- Exhaust all pairs of states: every causal edge runs forward in time. -/
macro "chrono_tac" : tactic =>
  `(tactic| (intro x y h; rcases x with x | x <;> cases x <;> rcases y with y | y <;>
      cases y <;> first | decide | exact absurd h (by decide)))

/-! ### Kind 1: the scarab -/

def scarabTime : Sum ScarabM ScarabP → Nat
  | .inl .dreamsOfScarab => 0
  | .inr .still => 0
  | .inr .beetleFlies => 1
  | .inl .recountsDream => 2
  | .inr .beetleTaps => 2
  | .inl .jungNotices => 3
  | .inr .jungCatchesBeetle => 4

/-- `0`: the consulting room; `1`: outside. -/
def scarabPlace : Sum ScarabM ScarabP → Nat
  | .inr .beetleFlies => 1
  | _ => 0

@[reducible] def scarabStaging : Staging scarabW := ⟨scarabTime, scarabPlace⟩

theorem scarab_chronological : Chronological scarabStaging := by chrono_tac

theorem scarab_kind :
    scarabStaging.kind ScarabM.recountsDream ScarabP.beetleTaps = Kind.coincident := by
  decide

/-! ### Kind 2: Swedenborg's fire -/

def swedTime : Sum SwedM SwedP → Nat
  | .inr .fireStarts => 0
  | .inl .visionOfFire => 1
  | .inr .fireSpreads => 1
  | .inl .tellsGuests => 2
  | .inr .fireStops => 2
  | .inl .newsArrives => 5

/-- `0`: Gothenburg; `1`: Stockholm. -/
def swedPlace : Sum SwedM SwedP → Nat
  | .inl _ => 0
  | .inr _ => 1

@[reducible] def swedStaging : Staging swedW := ⟨swedTime, swedPlace⟩

theorem swedenborg_chronological : Chronological swedStaging := by chrono_tac

theorem swedenborg_kind :
    swedStaging.kind SwedM.visionOfFire SwedP.fireSpreads = Kind.distant := by
  decide

/-! ### Kind 3: a precognitive dream (schematic)

A dream of an event that has not yet happened; the dreamer later learns of
the event through an ordinary report. Not tied to a particular anecdote. -/

inductive PrecogU | episode deriving DecidableEq, Repr
inductive PrecogM | dream | learnsOfEvent deriving DecidableEq, Repr
inductive PrecogP | event | report deriving DecidableEq, Repr

def precogEdge : Sum PrecogM PrecogP → Sum PrecogM PrecogP → Bool
  | .inr .event, .inr .report => true
  | .inr .report, .inl .learnsOfEvent => true
  | _, _ => false

/-- `true`: the dream; `false`: the event and the news of it. -/
def precogSide : Sum PrecogM PrecogP → Bool
  | .inl .dream => true
  | _ => false

@[reducible] def precogW : Model where
  U := PrecogU
  M := PrecogM
  P := PrecogP
  A := Arch
  ψ := fun _ => PrecogM.dream
  φ := fun _ => PrecogP.event
  causes := fun x y => precogEdge x y = true
  constellated := fun a _ => a = Arch.death
  expressesM := fun a m => a = Arch.death ∧ m = PrecogM.dream
  expressesP := fun a p => a = Arch.death ∧ p = PrecogP.event

def precogTime : Sum PrecogM PrecogP → Nat
  | .inl .dream => 0
  | .inr .event => 1
  | .inr .report => 2
  | .inl .learnsOfEvent => 3

@[reducible] def precogStaging : Staging precogW := ⟨precogTime, fun _ => 0⟩

theorem precog_sync : Synchronicity precogW PrecogM.dream PrecogP.event :=
  sync_of_separated precogW precogSide (by sep_tac) Arch.death PrecogU.episode
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)

theorem precog_chronological : Chronological precogStaging := by chrono_tac

theorem precog_kind :
    precogStaging.kind PrecogM.dream PrecogP.event = Kind.precognitive := by
  decide

/-- The dream is not an effect of the event it anticipates, and this follows
from chronology alone. -/
theorem precog_not_retrocausal :
    ¬ Path precogW.causes (.inr PrecogP.event) (.inl PrecogM.dream) :=
  no_retrocausation precogStaging precog_chronological (by decide)

/-- All three of Jung's kinds are realized by synchronicities. -/
theorem three_kinds_realized :
    (Synchronicity scarabW ScarabM.recountsDream ScarabP.beetleTaps ∧
      scarabStaging.kind ScarabM.recountsDream ScarabP.beetleTaps = Kind.coincident) ∧
    (Synchronicity swedW SwedM.visionOfFire SwedP.fireSpreads ∧
      swedStaging.kind SwedM.visionOfFire SwedP.fireSpreads = Kind.distant) ∧
    (Synchronicity precogW PrecogM.dream PrecogP.event ∧
      precogStaging.kind PrecogM.dream PrecogP.event = Kind.precognitive) :=
  ⟨⟨scarab_sync, scarab_kind⟩, ⟨swedenborg_sync, swedenborg_kind⟩,
   ⟨precog_sync, precog_kind⟩⟩

end PauliJung
