import PauliJung.Cases

/-!
# Axiom audit

Each headline theorem is pinned to the exact axioms it uses. The build fails
if any of them starts depending on `sorryAx` or on an axiom not listed here.
Only Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`)
appear, and the structural core uses none at all.
-/

open PauliJung

/-- info: 'PauliJung.no_sync_under_reichenbach' does not depend on any axioms -/
#guard_msgs in
#print axioms no_sync_under_reichenbach

/-- info: 'PauliJung.noLink_iff_ancestral' does not depend on any axioms -/
#guard_msgs in
#print axioms noLink_iff_ancestral

/-- info: 'PauliJung.sync_iff_ancestral' does not depend on any axioms -/
#guard_msgs in
#print axioms sync_iff_ancestral

/-- info: 'PauliJung.sync_antitone' does not depend on any axioms -/
#guard_msgs in
#print axioms sync_antitone

/-- info: 'PauliJung.lucadou' does not depend on any axioms -/
#guard_msgs in
#print axioms lucadou

/-- info: 'PauliJung.locked_aspects_correlate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms locked_aspects_correlate

/-- info: 'PauliJung.neutral_screens_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms neutral_screens_off

/-- info: 'PauliJung.ground_without_cause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ground_without_cause

/-- info: 'PauliJung.sync_without_any_reduction' does not depend on any axioms -/
#guard_msgs in
#print axioms sync_without_any_reduction

/-- info: 'PauliJung.meaning_without_sync' does not depend on any axioms -/
#guard_msgs in
#print axioms meaning_without_sync

/-- info: 'PauliJung.strict_not_content' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms strict_not_content

/-- info: 'PauliJung.scarab_collider_sync' does not depend on any axioms -/
#guard_msgs in
#print axioms scarab_collider_sync

/-- info: 'PauliJung.iching_content_sync' depends on axioms: [propext] -/
#guard_msgs in
#print axioms iching_content_sync

/-- info: 'PauliJung.scorecard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scorecard

