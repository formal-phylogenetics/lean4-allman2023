module

public import Mathlib.Data.Set.Image

/-!
# The image of a complement in a subtype
-/

@[expose] public section

namespace Set

/-- The elements of `F` other than `e`, as a subset of the ambient type. -/
theorem image_val_compl_singleton {α : Type*} {F : Set α} (e : F) :
    Subtype.val '' ({e}ᶜ : Set F) = F \ {e.1} := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, fun h => hg (Subtype.ext h)⟩
  · rintro ⟨hf, hne⟩
    exact ⟨⟨f, hf⟩, fun h => hne (congrArg Subtype.val h), rfl⟩

end Set
