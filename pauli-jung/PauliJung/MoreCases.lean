import PauliJung.Applications

/-!
# Further cases

Four more anecdotes, each analysed by the decision procedure. As before,
"synchronicity" means: synchronistic *in the stated model*. The causal
edges and the assignment of archetypes are modelling choices, and the
retellings are schematic.
-/

namespace PauliJung

/-! ### 11. The fox in the wood (told by Jung)

Walking in a wood, a patient tells Jung of a childhood dream of a spectral
fox; a fox comes out of the trees and walks ahead of them on the path. -/

inductive FoxU | walk deriving DecidableEq, Repr
inductive FoxM | tellsFoxDream | bothSeeFox deriving DecidableEq, Repr
inductive FoxP | foxInWood | foxOnPath deriving DecidableEq, Repr

def foxEdge : Sum FoxM FoxP → Sum FoxM FoxP → Bool
  | .inr .foxInWood, .inr .foxOnPath => true
  | .inr .foxOnPath, .inl .bothSeeFox => true
  | _, _ => false

@[reducible] def foxW : Model where
  U := FoxU
  M := FoxM
  P := FoxP
  A := Arch
  ψ := fun _ => FoxM.tellsFoxDream
  φ := fun _ => FoxP.foxOnPath
  causes := fun x y => foxEdge x y = true
  constellated := fun a _ => a = Arch.animal
  expressesM := fun a m => a = Arch.animal ∧ m = FoxM.tellsFoxDream
  expressesP := fun a p => a = Arch.animal ∧ p = FoxP.foxOnPath

def foxFull : FullPresentation foxW where
  nodes := [.inl .tellsFoxDream, .inl .bothSeeFox, .inr .foxInWood, .inr .foxOnPath]
  edge := foxEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl
  neutrals := [.walk]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

theorem fox_sync : Synchronicity foxW FoxM.tellsFoxDream FoxP.foxOnPath :=
  (foxFull.sync_iff_syncB _ _).2 (by decide)

/-! ### 12. The clock that stops at a death (a motif Jung mentions)

A clock stops at the hour its owner dies. The clock stops for mechanical
reasons of its own; the household only notices afterwards. -/

inductive ClockU | hourOfDeath deriving DecidableEq, Repr
inductive ClockM | ownerDying | householdNotices deriving DecidableEq, Repr
inductive ClockP | mechanismRunsDown | clockStops deriving DecidableEq, Repr

def clockEdge : Sum ClockM ClockP → Sum ClockM ClockP → Bool
  | .inr .mechanismRunsDown, .inr .clockStops => true
  | .inr .clockStops, .inl .householdNotices => true
  | _, _ => false

@[reducible] def clockW : Model where
  U := ClockU
  M := ClockM
  P := ClockP
  A := Arch
  ψ := fun _ => ClockM.ownerDying
  φ := fun _ => ClockP.clockStops
  causes := fun x y => clockEdge x y = true
  constellated := fun a _ => a = Arch.death
  expressesM := fun a m => a = Arch.death ∧ m = ClockM.ownerDying
  expressesP := fun a p => a = Arch.death ∧ p = ClockP.clockStops

def clockFull : FullPresentation clockW where
  nodes := [.inl .ownerDying, .inl .householdNotices,
    .inr .mechanismRunsDown, .inr .clockStops]
  edge := clockEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl
  neutrals := [.hourOfDeath]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

theorem clock_sync : Synchronicity clockW ClockM.ownerDying ClockP.clockStops :=
  (clockFull.sync_iff_syncB _ _).2 (by decide)

/-! ### 13. Kammerer's series

Paul Kammerer collected runs of like events, such as the same number turning
up on unrelated tickets the same day. Jung's objection: a run with no
meaning is only a run. Here nothing causal links the events, and no
archetype is constellated. -/

inductive KammU | concert | cloakroom deriving DecidableEq, Repr
inductive KammM | idleAttention deriving DecidableEq, Repr
inductive KammP | concertTicketNine | cloakroomTicketNine deriving DecidableEq, Repr

def kammφ : KammU → KammP
  | .concert => .concertTicketNine
  | .cloakroom => .cloakroomTicketNine

@[reducible] def kammW : Model where
  U := KammU
  M := KammM
  P := KammP
  A := Arch
  ψ := fun _ => KammM.idleAttention
  φ := kammφ
  causes := fun x y => (fun _ _ => false : Sum KammM KammP → Sum KammM KammP → Bool) x y = true
  constellated := fun _ _ => False
  expressesM := fun _ _ => False
  expressesP := fun _ _ => False

def kammFull : FullPresentation kammW where
  nodes := [.inl .idleAttention, .inr .concertTicketNine, .inr .cloakroomTicketNine]
  edge := fun _ _ => false
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl
  neutrals := [.concert, .cloakroom]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

/-- **Acausal is not enough.** The series is causally unlinked and still no
synchronicity, because nothing gives it meaning. -/
theorem kammerer_acausal_not_sync :
    ¬ CausallyLinked kammW (.inl KammM.idleAttention) (.inr KammP.concertTicketNine) ∧
    ¬ Synchronicity kammW KammM.idleAttention KammP.concertTicketNine :=
  ⟨fun h => absurd ((kammFull.toPresentation.linked_iff' _ _).1 h) (by decide),
   fun h => absurd ((kammFull.sync_iff_syncB _ _).1 h) (by decide)⟩

/-! ### 14. The bookcase (Jung and Freud, 1909, as Jung tells it)

During an argument with Freud, Jung feels a heat in his diaphragm and a
loud report comes from the bookcase. Jung predicts a second report, and it
comes. The model is the sceptic's: both reports come from the drying wood,
and the prediction is prompted by the first report. -/

inductive BookU | firstReport | secondReport deriving DecidableEq, Repr
inductive BookM | feelsHeat | predictsSecond | freudStartled deriving DecidableEq, Repr
inductive BookP | woodDries | firstCrack | secondCrack deriving DecidableEq, Repr

def bookψ : BookU → BookM
  | .firstReport => .feelsHeat
  | .secondReport => .predictsSecond

def bookφ : BookU → BookP
  | .firstReport => .firstCrack
  | .secondReport => .secondCrack

def bookEdge : Sum BookM BookP → Sum BookM BookP → Bool
  | .inr .woodDries, .inr .firstCrack => true
  | .inr .woodDries, .inr .secondCrack => true
  | .inr .firstCrack, .inl .freudStartled => true
  | .inr .firstCrack, .inl .predictsSecond => true
  | _, _ => false

@[reducible] def bookW : Model where
  U := BookU
  M := BookM
  P := BookP
  A := Arch
  ψ := bookψ
  φ := bookφ
  causes := fun x y => bookEdge x y = true
  constellated := fun a _ => a = Arch.shadow
  expressesM := fun a m => a = Arch.shadow ∧ (m = BookM.feelsHeat ∨ m = BookM.predictsSecond)
  expressesP := fun a p => a = Arch.shadow ∧ (p = BookP.firstCrack ∨ p = BookP.secondCrack)

def bookFull : FullPresentation bookW where
  nodes := [.inl .feelsHeat, .inl .predictsSecond, .inl .freudStartled,
    .inr .woodDries, .inr .firstCrack, .inr .secondCrack]
  edge := bookEdge
  complete := by pres_tac
  faithful := fun _ _ => Iff.rfl
  neutrals := [.firstReport, .secondReport]
  archetypes := allArch
  neutrals_complete := by neutrals_tac
  archetypes_complete := allArch_complete

/-- The first report, with the heat Jung felt, is a synchronicity in this
model... -/
theorem bookcase_first_sync : Synchronicity bookW BookM.feelsHeat BookP.firstCrack :=
  (bookFull.sync_iff_syncB _ _).2 (by decide)

/-- ...but the fulfilled prediction is not: prediction and second report
share a common cause in the drying wood. The more striking half of the story
is the causally ordinary one. -/
theorem bookcase_second_not_sync :
    ¬ Synchronicity bookW BookM.predictsSecond BookP.secondCrack :=
  fun h => absurd ((bookFull.sync_iff_syncB _ _).1 h) (by decide)

/-- The link is specifically a common cause: neither event leads to the other. -/
theorem bookcase_common_cause :
    (∃ z, Path bookW.causes z (.inl BookM.predictsSecond) ∧
        Path bookW.causes z (.inr BookP.secondCrack)) ∧
    ¬ Controls bookW BookM.predictsSecond BookP.secondCrack :=
  ⟨⟨.inr BookP.woodDries,
      Path.tail (b := (Sum.inr BookP.firstCrack : Sum bookW.M bookW.P)) (Path.single rfl) rfl,
      Path.single rfl⟩,
   fun h => by
     have key : isMental (Sum.inl BookM.predictsSecond : Sum bookW.M bookW.P) = true →
         isMental (Sum.inr BookP.secondCrack : Sum bookW.M bookW.P) = true :=
       Path.invariant (I := fun a => isMental a = true)
         (fun a b hab ha => by
           rcases a with a | a <;> cases a <;> rcases b with b | b <;> cases b <;>
             first | rfl | exact absurd hab (by decide) | exact absurd ha (by decide)) h
     cases key rfl⟩

end PauliJung
