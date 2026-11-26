import PauliJung.Applications
import PauliJung.Typology
import PauliJung.Series

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

/-- info: 'PauliJung.Presentation.linked_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Presentation.linked_iff

/-- info: 'PauliJung.Presentation.sync_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Presentation.sync_iff

/-- info: 'PauliJung.parallelism_all_sync' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parallelism_all_sync

/-- info: 'PauliJung.epiphenomenal_no_control' does not depend on any axioms -/
#guard_msgs in
#print axioms epiphenomenal_no_control

/-- info: 'PauliJung.complementary_nonreductive' does not depend on any axioms -/
#guard_msgs in
#print axioms complementary_nonreductive

/-- info: 'PauliJung.Hom.sync_reflect' does not depend on any axioms -/
#guard_msgs in
#print axioms Hom.sync_reflect

/-- info: 'PauliJung.AboveChance.of_lower_baseline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AboveChance.of_lower_baseline

/-- info: 'PauliJung.exists_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_max

/-- info: 'PauliJung.fish_cluster_at_chance' does not depend on any axioms -/
#guard_msgs in
#print axioms fish_cluster_at_chance

/-- info: 'PauliJung.no_retrocausation' does not depend on any axioms -/
#guard_msgs in
#print axioms no_retrocausation

/-- info: 'PauliJung.anticipation_link_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms anticipation_link_iff

/-- info: 'PauliJung.three_kinds_realized' does not depend on any axioms -/
#guard_msgs in
#print axioms three_kinds_realized

/-- info: 'PauliJung.scarab_collider_decided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scarab_collider_decided

/-- info: 'PauliJung.pudding_decided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pudding_decided

/-- info: 'PauliJung.room137_sync_iff_meaningful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms room137_sync_iff_meaningful

/-- info: 'PauliJung.crossWorld_profile' depends on axioms: [propext] -/
#guard_msgs in
#print axioms crossWorld_profile

/-- info: 'PauliJung.interaction_with_sync' does not depend on any axioms -/
#guard_msgs in
#print axioms interaction_with_sync

/-- info: 'PauliJung.scarab_sync_from_refinement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scarab_sync_from_refinement

/-- info: 'PauliJung.certB_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms certB_true

/-- info: 'PauliJung.mem_anc_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_anc_iff

/-- info: 'PauliJung.Presentation.linked_iff'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Presentation.linked_iff'

/-- info: 'PauliJung.FullPresentation.sync_iff_syncB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FullPresentation.sync_iff_syncB

/-- info: 'PauliJung.scorecard_decided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scorecard_decided

