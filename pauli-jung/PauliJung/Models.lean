import PauliJung.Frequency
import PauliJung.Intervention

/-!
# Basic models

Small worlds that show the definitions are consistent and that the notions
introduced so far are independent of one another.
-/

namespace PauliJung


/-- The smallest world with a synchronicity: the axioms are consistent. -/
@[reducible] def toyWorld : Model where
  U := Unit
  M := Unit
  P := Unit
  A := Unit
  ψ := fun _ => ()
  φ := fun _ => ()
  causes := fun _ _ => False
  constellated := fun _ _ => True
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

theorem toyWorld_has_sync : Synchronicity toyWorld () () :=
  ⟨⟨(), (), trivial, rfl, rfl, trivial, trivial⟩,
    noLink_of_noCause toyWorld (fun _ _ h => h) _ _⟩

def evenFlag (u : Nat) : Bool := u % 2 == 0
def earlyFlag (u : Nat) : Bool := decide (u < 2)

/-- Chance baseline: unrelated events need not correlate (2·2 = 1·4). -/
theorem chance_baseline : ¬ PosCorr (List.range 4) evenFlag earlyFlag := by
  decide

/-- A non-reductive world: mind constant, matter varying. -/
@[reducible] def splitWorld : Model where
  U := Bool
  M := Unit
  P := Bool
  A := Unit
  ψ := fun _ => ()
  φ := id
  causes := fun _ _ => False
  constellated := fun _ _ => True
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

theorem splitWorld_not_reductive : ¬ PhysicalReducesToMental splitWorld := by
  intro ⟨f, hf⟩
  have h : true = false := (hf true).trans (hf false).symm
  cases h

theorem splitWorld_has_sync : Synchronicity splitWorld () true :=
  ⟨⟨(), true, trivial, rfl, rfl, trivial, trivial⟩,
    noLink_of_noCause splitWorld (fun _ _ h => h) _ _⟩

/-- **Synchronicity does not need reduction.** -/
theorem sync_without_reduction :
    ∃ W : Model, (∃ m p, Synchronicity W m p) ∧ ¬ PhysicalReducesToMental W :=
  ⟨splitWorld, ⟨(), true, splitWorld_has_sync⟩, splitWorld_not_reductive⟩

/-- Aspects that vary independently: neither reduces to the other. -/
@[reducible] def crossWorld : Model where
  U := Bool × Bool
  M := Bool
  P := Bool
  A := Unit
  ψ := Prod.fst
  φ := Prod.snd
  causes := fun _ _ => False
  constellated := fun _ _ => True
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

theorem crossWorld_not_idealist : ¬ PhysicalReducesToMental crossWorld := by
  intro ⟨f, hf⟩
  have h : true = false := (hf (true, true)).trans (hf (true, false)).symm
  cases h

theorem crossWorld_not_physicalist : ¬ MentalReducesToPhysical crossWorld := by
  intro ⟨g, hg⟩
  have h : true = false := (hg (true, true)).trans (hg (false, true)).symm
  cases h

/-- **Dual-aspect monism is non-reductive in both directions**, and still
supports synchronicity. -/
theorem sync_without_any_reduction :
    ∃ W : Model, (∃ m p, Synchronicity W m p) ∧
      ¬ PhysicalReducesToMental W ∧ ¬ MentalReducesToPhysical W :=
  ⟨crossWorld,
   ⟨true, true, ⟨⟨(), (true, true), trivial, rfl, rfl, trivial, trivial⟩,
      noLink_of_noCause crossWorld (fun _ _ h => h) _ _⟩⟩,
   crossWorld_not_idealist, crossWorld_not_physicalist⟩

/-- A fully causal world: mind causes matter. -/
@[reducible] def causalWorld : Model where
  U := Unit
  M := Unit
  P := Unit
  A := Unit
  ψ := fun _ => ()
  φ := fun _ => ()
  causes := fun x y => x = .inl () ∧ y = .inr ()
  constellated := fun _ _ => True
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

theorem causalWorld_reichenbach : ManifestReichenbach causalWorld :=
  fun _ => Or.inl (Path.single ⟨rfl, rfl⟩)

/-- **The conjecture is contingent.** There are worlds full of meaningful
coincidences in which none is a synchronicity. -/
theorem meaning_without_sync :
    ∃ W : Model, (∃ m p, MeaningfulCoincidence W m p) ∧
      ∀ m p, ¬ Synchronicity W m p :=
  ⟨causalWorld, ⟨(), (), (), (), trivial, rfl, rfl, trivial, trivial⟩,
   no_sync_under_reichenbach causalWorld causalWorld_reichenbach⟩

/-- Perfectly locked aspects without causation (psychophysical parallelism). -/
@[reducible] def lockWorld : Model where
  U := Bool
  M := Bool
  P := Bool
  A := Unit
  ψ := id
  φ := id
  causes := fun _ _ => False
  constellated := fun _ _ => True
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

theorem lockWorld_sync : Synchronicity lockWorld true true :=
  ⟨⟨(), true, trivial, rfl, rfl, trivial, trivial⟩,
    noLink_of_noCause lockWorld (fun _ _ h => h) _ _⟩

/-- **Strict does not imply content-level.** In the locked world the pair is
a strict synchronicity, but the mental content tracks the outcome, so it is
not a content synchronicity. (The converse failure is the I Ching case.) -/
theorem strict_not_content :
    Synchronicity lockWorld true true ∧
      ¬ ContentSynchronicity lockWorld [true, false] id id true :=
  ⟨lockWorld_sync,
   not_content_sync_of_locked lockWorld [true, false] id id (fun _ _ => rfl)
     (by decide) (by decide) true⟩

/-- Exploiting the toy synchronicity destroys it. -/
theorem toyWorld_exploited : ¬ Synchronicity (toyWorld.exploit () ()) () () :=
  exploit_destroys_sync toyWorld () ()

end PauliJung
