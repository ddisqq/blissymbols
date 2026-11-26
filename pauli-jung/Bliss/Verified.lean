import Bliss.Data

/-!
# The database is well-formed

Checked by the kernel on the generated data: no shape or character refers
to anything missing or to itself, directly or indirectly, and the same for
words. Consequently every character has a finite list of strokes and every
word a finite list of characters.
-/

namespace Bliss

set_option maxRecDepth 100000 in
/-- Shapes and characters are well-founded and use only existing paths. -/
theorem items_wf : wfFrom primNames.length 0 items = true := by decide

set_option maxRecDepth 100000 in
/-- Every character points at an existing item. -/
theorem chars_valid : chars.all (fun c => decide (c.item < items.length)) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Words are well-founded and use only existing characters. -/
theorem words_wf : wwfFrom chars.length 0 words = true := by decide

/-- Strokes of an item of the database. -/
def itemStrokes (i : Nat) (hi : i < items.length) : List Stroke :=
  flatten items items_wf i hi

/-- **No stroke of any symbol refers to a missing path.** -/
theorem itemStrokes_valid (i : Nat) (hi : i < items.length) :
    ∀ s ∈ itemStrokes i hi, s.prim < primNames.length :=
  flatten_prim_lt items items_wf i hi

/-- Characters of a word of the database, as indices into `chars`. -/
def wordChars (i : Nat) (hi : i < words.length) : List Nat :=
  expandWord words words_wf i hi

/-- **No word refers to a missing character.** -/
theorem wordChars_valid (i : Nat) (hi : i < words.length) :
    ∀ c ∈ wordChars i hi, c < chars.length :=
  expandWord_lt words words_wf i hi

end Bliss
