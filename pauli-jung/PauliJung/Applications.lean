import PauliJung.Cases
import PauliJung.Decide
import PauliJung.Positions
import PauliJung.Morphisms

/-!
# Applications: the general theory applied to the cases

* every case gets a finite presentation, and its verdict (causal link, and
  synchronicity itself) is recomputed by the verified decision procedure,
  independently of the hand-supplied certificates in `Cases`;
* the cases are located among the classical positions;
* the two scarab models are related by a morphism.
-/

namespace PauliJung

/-- Every state is in the list. -/
macro "pres_tac" : tactic =>
  `(tactic| (intro x; rcases x with x | x <;> cases x <;> simp))

/-! ### Presentations -/

def scarabPres : Presentation scarabW where
  nodes := [.inl .dreamsOfScarab, .inl .recountsDream, .inl .jungNotices,
    .inr .still, .inr .beetleFlies, .inr .beetleTaps, .inr .jungCatchesBeetle]
  edge := scarabEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def scarabColliderPres : Presentation scarabColliderW where
  nodes := scarabPres.nodes
  edge := scarabEdge2
  complete := scarabPres.complete
  faithful := fun _ _ => Iff.rfl

def pauliPres : Presentation pauliW where
  nodes := [.inl .pauliOnTrain, .inl .franckPuzzled,
    .inr .trainHalts, .inr .vacuumLeak, .inr .apparatusFails]
  edge := pauliEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def birdsPres : Presentation birdsW where
  nodes := [.inl .wifeAlarmed, .inr .birdsGather, .inr .heartFails, .inr .husbandCollapses]
  edge := birdsEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def swedPres : Presentation swedW where
  nodes := [.inl .visionOfFire, .inl .tellsGuests, .inl .newsArrives,
    .inr .fireStarts, .inr .fireSpreads, .inr .fireStops]
  edge := swedEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def puddingPres : Presentation puddingW where
  nodes := [.inl .tastesPudding, .inl .ordersPudding, .inl .remarksAbsence,
    .inr .fontgibuGivesPudding, .inr .lastPuddingTaken, .inr .wrongAddress,
    .inr .fontgibuEnters]
  edge := puddingEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def fishPres : Presentation fishW where
  nodes := [.inl .noticesFish, .inr .fishPresent]
  edge := fishEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def room137Pres : Presentation room137W where
  nodes := [.inl .computesAlpha, .inl .preoccupiedWith137,
    .inr .spectrumMeasured, .inr .illness, .inr .assignedRoom137]
  edge := r137Edge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

def ichingPres : Presentation ichingW where
  nodes := [.inl .asksAboutBook, .inr .coinsTossed, .inr .hexagram50]
  edge := ichingEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl

/-! ### Verdicts by computation -/

theorem scarab_decided :
    ¬ CausallyLinked scarabW (.inl ScarabM.recountsDream) (.inr ScarabP.beetleTaps) :=
  scarabPres.unlinked _ _ (by decide)

/-- The checker needs no hint that the observer is a collider. -/
theorem scarab_collider_decided :
    ¬ CausallyLinked scarabColliderW
      (.inl ScarabM.recountsDream) (.inr ScarabP.beetleTaps) :=
  scarabColliderPres.unlinked _ _ (by decide)

theorem pauli_decided :
    ¬ CausallyLinked pauliW (.inl PauliM.pauliOnTrain) (.inr PauliP.apparatusFails) :=
  pauliPres.unlinked _ _ (by decide)

theorem birds_decided :
    ¬ CausallyLinked birdsW (.inl BirdsM.wifeAlarmed) (.inr BirdsP.husbandCollapses) :=
  birdsPres.unlinked _ _ (by decide)

theorem swedenborg_decided :
    ¬ CausallyLinked swedW (.inl SwedM.visionOfFire) (.inr SwedP.fireSpreads) :=
  swedPres.unlinked _ _ (by decide)

theorem pudding_decided :
    ¬ CausallyLinked puddingW (.inl PuddingM.ordersPudding) (.inr PuddingP.lastPuddingTaken) ∧
    ¬ CausallyLinked puddingW (.inl PuddingM.remarksAbsence) (.inr PuddingP.fontgibuEnters) ∧
    CausallyLinked puddingW (.inl PuddingM.tastesPudding) (.inr PuddingP.fontgibuGivesPudding) :=
  ⟨puddingPres.unlinked _ _ (by decide), puddingPres.unlinked _ _ (by decide),
   puddingPres.linked _ _ (by decide)⟩

theorem fish_decided :
    CausallyLinked fishW (.inl FishM.noticesFish) (.inr FishP.fishPresent) :=
  fishPres.linked _ _ (by decide)

theorem room137_decided :
    ¬ CausallyLinked room137W (.inl R137M.preoccupiedWith137) (.inr R137P.assignedRoom137) ∧
    CausallyLinked room137W (.inl R137M.computesAlpha) (.inr R137P.spectrumMeasured) :=
  ⟨room137Pres.unlinked _ _ (by decide), room137Pres.linked _ _ (by decide)⟩

theorem iching_decided :
    CausallyLinked ichingW (.inl IChingM.asksAboutBook) (.inr IChingP.hexagram50) :=
  ichingPres.linked _ _ (by decide)

/-- In room 137 the checker turns synchronicity into a computation: the pair
is synchronistic exactly when it is meaningful. -/
theorem room137_sync_iff_meaningful :
    Synchronicity room137W R137M.preoccupiedWith137 R137P.assignedRoom137 ↔
      MeaningfulCoincidence room137W R137M.preoccupiedWith137 R137P.assignedRoom137 := by
  rw [room137Pres.sync_iff _ _ (by decide)]
  exact ⟨fun h => h.1, fun h => ⟨h, by decide⟩⟩

/-! ### Full presentations: synchronicity itself by computation -/

/-- All archetypes. -/
def allArch : List Arch :=
  [.rebirth, .shadow, .death, .fire, .series, .fish, .number, .wholeness, .psi, .union]

theorem allArch_complete (a : Arch) : a ∈ allArch := by cases a <;> simp [allArch]

/-- Every neutral state is in the list. -/
macro "neutrals_tac" : tactic => `(tactic| (intro u; cases u <;> simp))

def scarabFull : FullPresentation scarabW where
  toPresentation := scarabPres
  neutrals := [.before, .session]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def scarabColliderFull : FullPresentation scarabColliderW where
  toPresentation := scarabColliderPres
  neutrals := [.before, .session]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def pauliFull : FullPresentation pauliW where
  toPresentation := pauliPres
  neutrals := [.goettingen]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def birdsFull : FullPresentation birdsW where
  toPresentation := birdsPres
  neutrals := [.deathDay]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def swedFull : FullPresentation swedW where
  toPresentation := swedPres
  neutrals := [.evening1759]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def puddingFull : FullPresentation puddingW where
  toPresentation := puddingPres
  neutrals := [.boyhood, .restaurant, .dinner]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def fishFull : FullPresentation fishW where
  toPresentation := fishPres
  neutrals := [.lunch, .inscription, .pictures, .embroidery]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def room137Full : FullPresentation room137W where
  toPresentation := room137Pres
  neutrals := [.physicsYears, .dec1958]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

def ichingFull : FullPresentation ichingW where
  toPresentation := ichingPres
  neutrals := [.consultation]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

/-- **The strict scorecard, recomputed.** Every verdict on strict
synchronicity in the case table is obtained by running the decision
procedure, with no hand-supplied certificate. -/
theorem scorecard_decided :
    Synchronicity scarabW ScarabM.recountsDream ScarabP.beetleTaps ∧
    Synchronicity scarabColliderW ScarabM.recountsDream ScarabP.beetleTaps ∧
    Synchronicity pauliW PauliM.pauliOnTrain PauliP.apparatusFails ∧
    Synchronicity birdsW BirdsM.wifeAlarmed BirdsP.husbandCollapses ∧
    Synchronicity swedW SwedM.visionOfFire SwedP.fireSpreads ∧
    Synchronicity puddingW PuddingM.ordersPudding PuddingP.lastPuddingTaken ∧
    Synchronicity puddingW PuddingM.remarksAbsence PuddingP.fontgibuEnters ∧
    ¬ Synchronicity puddingW PuddingM.tastesPudding PuddingP.fontgibuGivesPudding ∧
    ¬ Synchronicity fishW FishM.noticesFish FishP.fishPresent ∧
    Synchronicity room137W R137M.preoccupiedWith137 R137P.assignedRoom137 ∧
    ¬ Synchronicity room137W R137M.computesAlpha R137P.spectrumMeasured ∧
    ¬ Synchronicity ichingW IChingM.asksAboutBook IChingP.hexagram50 :=
  ⟨(scarabFull.sync_iff_syncB _ _).2 (by decide),
   (scarabColliderFull.sync_iff_syncB _ _).2 (by decide),
   (pauliFull.sync_iff_syncB _ _).2 (by decide),
   (birdsFull.sync_iff_syncB _ _).2 (by decide),
   (swedFull.sync_iff_syncB _ _).2 (by decide),
   (puddingFull.sync_iff_syncB _ _).2 (by decide),
   (puddingFull.sync_iff_syncB _ _).2 (by decide),
   fun h => absurd ((puddingFull.sync_iff_syncB _ _).1 h) (by decide),
   fun h => absurd ((fishFull.sync_iff_syncB _ _).1 h) (by decide),
   (room137Full.sync_iff_syncB _ _).2 (by decide),
   fun h => absurd ((room137Full.sync_iff_syncB _ _).1 h) (by decide),
   fun h => absurd ((ichingFull.sync_iff_syncB _ _).1 h) (by decide)⟩

/-- The decision procedure also finds the pairs nobody listed: in the scarab
world, the dream itself (before the session) coincides with nothing. -/
theorem scarab_dream_not_sync :
    ¬ Synchronicity scarabW ScarabM.dreamsOfScarab ScarabP.still :=
  fun h => absurd ((scarabFull.sync_iff_syncB _ _).1 h) (by decide)

/-! ### The cases among the positions -/

/-- The scarab world is interactionist: perception runs from matter to mind,
action from mind to matter. Synchronicity does not need parallelism. -/
theorem scarab_interactionist : Interactionist scarabW :=
  ⟨⟨ScarabM.jungNotices, ScarabP.jungCatchesBeetle, rfl⟩,
   ⟨ScarabP.beetleTaps, ScarabM.jungNotices, rfl⟩⟩

theorem interaction_with_sync :
    ∃ W : Model, Interactionist W ∧ ∃ m p, Synchronicity W m p :=
  ⟨scarabW, scarab_interactionist, _, _, scarab_sync⟩

/-- The Pauli-effect world as modelled is epiphenomenal: Pauli's mind does
nothing to the apparatus, directly or indirectly. -/
theorem pauli_epiphenomenal : Epiphenomenal pauliW := by
  intro m p h
  cases m <;> cases p <;> exact absurd h (by decide)

theorem pauli_no_control :
    ¬ Controls pauliW PauliM.pauliOnTrain PauliP.apparatusFails :=
  epiphenomenal_no_control pauliW pauli_epiphenomenal _ _

/-- The idealized Rhine world is parallelist. -/
theorem rhine_parallelist : Parallelist rhineW := fun _ _ h => absurd h id

theorem crossWorld_complementary : Complementary crossWorld :=
  fun u v => ⟨(u.1, v.2), rfl, rfl⟩

/-- A world that is complementary, non-reductive both ways, parallelist, and
in which every aspect pair is a synchronicity. -/
theorem crossWorld_profile :
    Complementary crossWorld ∧ Parallelist crossWorld ∧
      ¬ PhysicalReducesToMental crossWorld ∧ ¬ MentalReducesToPhysical crossWorld ∧
      ∀ u, Synchronicity crossWorld (crossWorld.ψ u) (crossWorld.φ u) :=
  ⟨crossWorld_complementary, fun _ _ h => absurd h id,
   crossWorld_not_idealist, crossWorld_not_physicalist,
   fun u => parallelism_all_sync crossWorld (fun _ _ h => absurd h id)
     ⟨(), u, trivial, rfl, rfl, trivial, trivial⟩⟩

/-! ### A morphism between the two scarab models -/

/-- The plain scarab world maps into the one with Jung as common observer. -/
def scarabRefine : Hom scarabW scarabColliderW :=
  Hom.ofWithCauses scarabW (fun x y => scarabEdge2 x y = true)
    (fun x y h => by
      have h' : scarabEdge x y = true := h
      simp [scarabEdge2, h'])

/-- The synchronicity of the richer model implies that of the plainer one. -/
theorem scarab_sync_from_refinement :
    Synchronicity scarabW ScarabM.recountsDream ScarabP.beetleTaps :=
  scarabRefine.sync_reflect scarab_sync.1 scarab_collider_sync

end PauliJung
