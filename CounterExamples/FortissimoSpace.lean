import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

/-!
# Fortissimo Space
In a universe of elements of type u, which is not countable, we define a topology on u, called the Fortissimo Space. Let $p$ be a particular element of u. A set $X$ is open in the Fortissimo Space if either $p$ is contained in the complement of $X$ or the complement of $X$ is countable.

* We show that the Fortissimo Space is a T1 Space.

-/


/--Making the Fortissimo Space-/
def FortissiomoSpace_mk{α : Type u}(p : α) : TopologicalSpace α where
  IsOpen X := p ∈ Xᶜ  ∨ Set.Countable Xᶜ
  isOpen_univ := by
    simp only [compl_univ, mem_empty_iff_false, countable_empty, or_true]
  isOpen_inter := by
    simp only [mem_inter_iff]
    intro s t hs ht
    cases hs with
    | inl hps  =>
      left
      rw[Set.compl_inter]
      simp only [mem_union]
      left
      assumption
    | inr hcs =>
      cases ht with
      | inl hpt =>
        left
        rw[Set.compl_inter]
        simp only [mem_union]
        right
        assumption
      | inr hct =>
        right
        rw[Set.compl_inter]
        apply Set.Countable.union hcs hct
  isOpen_sUnion := by
    simp only [mem_sUnion]
    intro s hs
    by_cases hp : p ∈ (⋃₀ s)ᶜ
    · left
      assumption
    · right
      simp only [mem_compl_iff, mem_sUnion, not_exists, not_and, not_forall, not_not, exists_prop] at hp
      cases hp with
      | intro t ht =>
        have hsc : Set.Countable tᶜ :=by
          have hpt : ¬ (p ∈ tᶜ) := by
            intro hpt
            apply hpt ht.2
          apply Or.resolve_left (hs t ht.1) hpt
        have hst :  (⋃₀ s)ᶜ ⊆ tᶜ  := by
          rw[Set.compl_subset_compl]
          intro x hx
          rw[Set.mem_sUnion]
          use t
          exact ⟨ht.1, hx⟩
        exact Set.Countable.mono hst hsc

section FortissiomoSpace

variable{α : Type u}(p : α)(hcount : ¬ Countable α)[t : TopologicalSpace α](topology_eq : t = FortissiomoSpace_mk p)

/--Fortissimo Space is open if either p is contained in the complement of X or complement of X is countable-/
theorem FS_open_iff : IsOpen X = (p ∈ Xᶜ  ∨ Set.Countable Xᶜ) := by
  rw[topology_eq]
  rfl

/--Fortissimo Space is a T1 Space-/
instance FS_T₁ : T1Space α := by
  rw[t1Space_iff_exists_open]
  intros x y hxy
  by_cases hp :y = p ∨ x = p
  · cases hp with
    | inl hpy =>
        set U : Set α := {p}ᶜ  with hU
        use U
        constructor
        rw[FS_open_iff p topology_eq]
        left
        rw[hU]
        simp
        constructor
        rw[hU]
        simp only [mem_compl_iff, mem_singleton_iff]
        rw[hpy] at hxy
        exact hxy
        rw[hpy,hU]
        simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, not_false_eq_true]
    | inr hpx =>
        set U : Set α := {y}ᶜ  with hU
        use U
        constructor
        rw[FS_open_iff p topology_eq]
        right
        rw[hU]
        simp only [compl_compl, countable_singleton]
        rw[hU]
        simp
        exact hxy
  push_neg at hp
  set U : Set α := {y,p}ᶜ with hU
  use U
  constructor
  rw[FS_open_iff p topology_eq]
  left
  rw[hU]
  simp only [mem_singleton_iff, compl_compl, mem_insert_iff, or_true]
  constructor
  rw[hU]
  simp only [mem_singleton_iff, mem_compl_iff, mem_insert_iff]
  push_neg
  exact ⟨hxy,hp.2⟩
  rw[hU]
  simp only [mem_singleton_iff, mem_compl_iff, mem_insert_iff, true_or, not_true_eq_false,
    not_false_eq_true]

/--Fortissimo Space is a T5 Space-/
instance FS_T₅ : T5Space α := by

  sorry

end FortissiomoSpace
