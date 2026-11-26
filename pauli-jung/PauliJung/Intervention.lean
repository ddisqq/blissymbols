import PauliJung.Core

/-!
# Intervention: exploiting a synchronicity destroys it

Lucadou's reading of the no-signalling condition: a synchronistic
correlation cannot be used as a signal, and the attempt to use it turns it
into something else. Formally, adding causes to a world can only remove
synchronicities, and adding the one cause that would make `m` steer `p`
removes the synchronicity of `m` and `p` while leaving their meaning intact.
-/

namespace PauliJung

variable (W : Model)

/-- The same world with a different causal relation. -/
@[reducible] def Model.withCauses (W : Model)
    (c : Sum W.M W.P → Sum W.M W.P → Prop) : Model :=
  { W with causes := c }

/-- Causal links survive when causes are added. -/
theorem CausallyLinked.mono (c : Sum W.M W.P → Sum W.M W.P → Prop)
    (hc : ∀ x y, W.causes x y → c x y) {x y : Sum W.M W.P}
    (h : CausallyLinked W x y) : CausallyLinked (W.withCauses c) x y := by
  rcases h with h | h | ⟨z, hzx, hzy⟩
  · exact Or.inl (Path.mono hc h)
  · exact Or.inr (Or.inl (Path.mono hc h))
  · exact Or.inr (Or.inr ⟨z, Path.mono hc hzx, Path.mono hc hzy⟩)

/-- **Synchronicity is fragile.** Adding causes never creates a
synchronicity: whatever is synchronistic in the richer world already was in
the poorer one. -/
theorem sync_antitone (c : Sum W.M W.P → Sum W.M W.P → Prop)
    (hc : ∀ x y, W.causes x y → c x y) {m : W.M} {p : W.P}
    (h : Synchronicity (W.withCauses c) m p) : Synchronicity W m p :=
  ⟨h.1, fun hl => h.2 (CausallyLinked.mono W c hc hl)⟩

/-- Meaning does not depend on the causal relation. -/
theorem meaningful_withCauses (c : Sum W.M W.P → Sum W.M W.P → Prop)
    {m : W.M} {p : W.P} :
    MeaningfulCoincidence (W.withCauses c) m p ↔ MeaningfulCoincidence W m p :=
  Iff.rfl

/-- The world in which `m` is used to steer `p`. -/
@[reducible] def Model.exploit (W : Model) (m : W.M) (p : W.P) : Model :=
  W.withCauses (fun x y => W.causes x y ∨ (x = .inl m ∧ y = .inr p))

/-- In the exploited world, `m` controls `p`. -/
theorem exploit_controls (m : W.M) (p : W.P) : Controls (W.exploit m p) m p :=
  Path.single (Or.inr ⟨rfl, rfl⟩)

/-- **Exploitation destroys synchronicity.** -/
theorem exploit_destroys_sync (m : W.M) (p : W.P) :
    ¬ Synchronicity (W.exploit m p) m p :=
  fun h => sync_no_signal (W.exploit m p) h (exploit_controls W m p)

/-- **Lucadou's principle.** Turning a synchronicity into a signal keeps the
meaningful coincidence but ends the synchronicity. -/
theorem lucadou {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    MeaningfulCoincidence (W.exploit m p) m p ∧
      ¬ Synchronicity (W.exploit m p) m p :=
  ⟨h.1, exploit_destroys_sync W m p⟩

/-- Exploiting one pair cannot create a synchronicity anywhere else. -/
theorem exploit_creates_nothing (m : W.M) (p : W.P) {m' : W.M} {p' : W.P}
    (h : Synchronicity (W.exploit m p) m' p') : Synchronicity W m' p' :=
  sync_antitone W _ (fun _ _ hxy => Or.inl hxy) h

end PauliJung
