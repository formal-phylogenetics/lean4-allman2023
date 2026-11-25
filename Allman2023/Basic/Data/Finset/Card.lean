module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith

/-!
# Finite sets of a given small cardinality

Facts about sets of two, four and five elements, written with explicit elements: the elements of a
set of five are distinct, a set of four has four names, and four elements of a type of four are all
of them.
-/

@[expose] public section

open Finset

variable {α : Type*}

namespace Finset

variable [DecidableEq α]

/-- The five elements of a set of five are pairwise distinct. -/
theorem ne_of_card_eq_five {a b c d e : α} (h : ({a, b, c, d, e} : Finset α).card = 5) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  have key : ∀ u v w z t : α, ({u, v, w, z, t} : Finset α).card = 5 → u ≠ v := by
    rintro u v w z t h rfl
    have : ({u, u, w, z, t} : Finset α).card ≤ 4 := by
      rw [Finset.insert_idem]; exact Finset.card_le_four
    omega
  refine ⟨key _ _ _ _ _ h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply key a c b d e; rw [← h]; congr 1; grind
  · apply key a d b c e; rw [← h]; congr 1; grind
  · apply key a e b c d; rw [← h]; congr 1; grind
  · apply key b c a d e; rw [← h]; congr 1; grind
  · apply key b d a c e; rw [← h]; congr 1; grind
  · apply key b e a c d; rw [← h]; congr 1; grind
  · apply key c d a b e; rw [← h]; congr 1; grind
  · apply key c e a b d; rw [← h]; congr 1; grind
  · apply key d e a b c; rw [← h]; congr 1; grind

omit [DecidableEq α] in
/-- A set of four elements has two distinct ones. -/
theorem nontrivial_coe_of_card_eq_four {Q : Finset α} (hQ : Q.card = 4) : (Q : Set α).Nontrivial :=
  Finset.one_lt_card_iff_nontrivial.mp (by omega)

/-- A set of four elements, named. -/
theorem exists_eq_of_card_eq_four {Q : Finset α} (h : Q.card = 4) :
    ∃ a b c d : α, ({a, b, c, d} : Finset α) = Q := by
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp h
  obtain ⟨b, c, d, -, -, -, rfl⟩ := Finset.card_eq_three.mp ht
  exact ⟨a, b, c, d, rfl⟩

/-- In a set of two elements, an element other than one of two distinct elements of the set is the
other. -/
theorem eq_of_mem_of_card_eq_two {S : Finset α} (hS : #S = 2) {a b c : α} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a ≠ b) (hca : c ≠ a) : c = b := by
  obtain ⟨u, v, -, rfl⟩ := card_eq_two.1 hS
  simp only [mem_insert, mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first
    | rfl
    | exact absurd rfl hab
    | exact absurd rfl hca

end Finset

namespace Fintype

variable [Fintype α]

/-- A type of four elements has two distinct ones. -/
theorem nontrivial_of_card_eq_four (h : Fintype.card α = 4) : Nontrivial α :=
  Fintype.one_lt_card_iff_nontrivial.mp (by omega)

variable [DecidableEq α]

/-- Four distinct elements of a type of four are all of them. -/
theorem eq_or_eq_or_eq_or_eq_of_card_eq_four (hcard : Fintype.card α = 4) {a b c d : α}
    (h : ({a, b, c, d} : Finset α).card = 4) (x : α) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  have hu : ({a, b, c, d} : Finset α) = Finset.univ := Finset.eq_univ_of_card _ (h.trans hcard.symm)
  have := Finset.mem_univ x
  rw [← hu] at this
  simpa using this

/-- A type of four elements has four distinct ones. -/
theorem exists_card_eq_four (hcard : Fintype.card α = 4) :
    ∃ a b c d : α, ({a, b, c, d} : Finset α).card = 4 := by
  have hu : (Finset.univ : Finset α).card = 4 := by rw [Finset.card_univ, hcard]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (Finset.univ : Finset α).card by omega)
  obtain ⟨b, c, d, -, -, -, he⟩ := Finset.card_eq_three.mp
    (by rw [Finset.card_erase_of_mem ha, hu] : ((Finset.univ : Finset α).erase a).card = 3)
  refine ⟨a, b, c, d, ?_⟩
  rw [← he, Finset.insert_erase ha, hu]

end Fintype
