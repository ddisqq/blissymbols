import PauliJung.Intervention

/-!
# Morphisms of dual-aspect worlds

A morphism maps one world into another, respecting aspects, meaning and
causes. Typical uses: embedding a fragment of a story into a fuller one,
or coarse-graining a detailed description into a schematic one.

Because causes are preserved forwards, causal links are too, so the
*absence* of a link travels backwards: if the image of a meaningful
coincidence is synchronistic, the original was.
-/

namespace PauliJung

/-- A structure-preserving map of worlds. -/
structure Hom (W W' : Model) where
  fU : W.U → W'.U
  fM : W.M → W'.M
  fP : W.P → W'.P
  fA : W.A → W'.A
  ψ_comm : ∀ u, W'.ψ (fU u) = fM (W.ψ u)
  φ_comm : ∀ u, W'.φ (fU u) = fP (W.φ u)
  constellated_map : ∀ a u, W.constellated a u → W'.constellated (fA a) (fU u)
  expressesM_map : ∀ a m, W.expressesM a m → W'.expressesM (fA a) (fM m)
  expressesP_map : ∀ a p, W.expressesP a p → W'.expressesP (fA a) (fP p)
  causes_map : ∀ x y, W.causes x y →
    W'.causes (Sum.elim (fun m => .inl (fM m)) (fun p => .inr (fP p)) x)
              (Sum.elim (fun m => .inl (fM m)) (fun p => .inr (fP p)) y)

namespace Hom

variable {W W' W'' : Model}

/-- The action on manifest states. -/
def onStates (f : Hom W W') : Sum W.M W.P → Sum W'.M W'.P :=
  Sum.elim (fun m => .inl (f.fM m)) (fun p => .inr (f.fP p))

/-- The identity morphism. -/
def id (W : Model) : Hom W W where
  fU := fun u => u
  fM := fun m => m
  fP := fun p => p
  fA := fun a => a
  ψ_comm := fun _ => rfl
  φ_comm := fun _ => rfl
  constellated_map := fun _ _ h => h
  expressesM_map := fun _ _ h => h
  expressesP_map := fun _ _ h => h
  causes_map := fun x y h => by cases x <;> cases y <;> exact h

/-- Composition of morphisms. -/
def comp (g : Hom W' W'') (f : Hom W W') : Hom W W'' where
  fU := fun u => g.fU (f.fU u)
  fM := fun m => g.fM (f.fM m)
  fP := fun p => g.fP (f.fP p)
  fA := fun a => g.fA (f.fA a)
  ψ_comm := fun u => by rw [g.ψ_comm, f.ψ_comm]
  φ_comm := fun u => by rw [g.φ_comm, f.φ_comm]
  constellated_map := fun a u h => g.constellated_map _ _ (f.constellated_map a u h)
  expressesM_map := fun a m h => g.expressesM_map _ _ (f.expressesM_map a m h)
  expressesP_map := fun a p h => g.expressesP_map _ _ (f.expressesP_map a p h)
  causes_map := fun x y h => by
    have := g.causes_map _ _ (f.causes_map x y h)
    cases x <;> cases y <;> exact this

/-- Morphisms carry causal paths forward. -/
theorem path_map (f : Hom W W') {x y : Sum W.M W.P} (p : Path W.causes x y) :
    Path W'.causes (f.onStates x) (f.onStates y) := by
  induction p with
  | single hab => exact Path.single (f.causes_map _ _ hab)
  | tail _ hbc ih => exact Path.tail ih (f.causes_map _ _ hbc)

/-- Morphisms carry causal links forward. -/
theorem linked_map (f : Hom W W') {x y : Sum W.M W.P} (h : CausallyLinked W x y) :
    CausallyLinked W' (f.onStates x) (f.onStates y) := by
  rcases h with h | h | ⟨z, hzx, hzy⟩
  · exact Or.inl (f.path_map h)
  · exact Or.inr (Or.inl (f.path_map h))
  · exact Or.inr (Or.inr ⟨f.onStates z, f.path_map hzx, f.path_map hzy⟩)

/-- Morphisms carry meaningful coincidences forward. -/
theorem meaningful_map (f : Hom W W') {m : W.M} {p : W.P}
    (h : MeaningfulCoincidence W m p) : MeaningfulCoincidence W' (f.fM m) (f.fP p) := by
  obtain ⟨a, u, hc, hm, hp, hem, hep⟩ := h
  exact ⟨f.fA a, f.fU u, f.constellated_map a u hc,
    by rw [f.ψ_comm, hm], by rw [f.φ_comm, hp],
    f.expressesM_map a m hem, f.expressesP_map a p hep⟩

/-- **Acausality is reflected.** If the images are unlinked, so were the
originals. -/
theorem noLink_reflect (f : Hom W W') {m : W.M} {p : W.P}
    (h : ¬ CausallyLinked W' (.inl (f.fM m)) (.inr (f.fP p))) :
    ¬ CausallyLinked W (.inl m) (.inr p) :=
  fun hl => h (f.linked_map hl)

/-- **Synchronicity is reflected.** A meaningful coincidence whose image is
a synchronicity is itself one. Seen the other way round: refining a
description (adding causal detail) can only dissolve synchronicities. -/
theorem sync_reflect (f : Hom W W') {m : W.M} {p : W.P}
    (hm : MeaningfulCoincidence W m p) (h : Synchronicity W' (f.fM m) (f.fP p)) :
    Synchronicity W m p :=
  ⟨hm, f.noLink_reflect h.2⟩

/-- An ordinary (causal) coincidence stays ordinary under any morphism. -/
theorem not_sync_map (f : Hom W W') {m : W.M} {p : W.P}
    (h : CausallyLinked W (.inl m) (.inr p)) : ¬ Synchronicity W' (f.fM m) (f.fP p) :=
  fun hs => hs.2 (f.linked_map h)

/-- Adding causes is a morphism from the poorer world to the richer one. -/
def ofWithCauses (W : Model) (c : Sum W.M W.P → Sum W.M W.P → Prop)
    (hc : ∀ x y, W.causes x y → c x y) : Hom W (W.withCauses c) where
  fU := fun u => u
  fM := fun m => m
  fP := fun p => p
  fA := fun a => a
  ψ_comm := fun _ => rfl
  φ_comm := fun _ => rfl
  constellated_map := fun _ _ h => h
  expressesM_map := fun _ _ h => h
  expressesP_map := fun _ _ h => h
  causes_map := fun x y h => by cases x <;> cases y <;> exact hc _ _ h

/-- `sync_antitone` recovered as an instance of reflection. -/
theorem sync_antitone' (W : Model) (c : Sum W.M W.P → Sum W.M W.P → Prop)
    (hc : ∀ x y, W.causes x y → c x y) {m : W.M} {p : W.P}
    (h : Synchronicity (W.withCauses c) m p) : Synchronicity W m p :=
  (ofWithCauses W c hc).sync_reflect h.1 h

end Hom

end PauliJung
