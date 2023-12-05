import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w

/-!
# Fortissimo Space
In a universe of elements of type u, which is not countable, we define a topology on u, called the Fortissimo Space. Let `p` be a particular element of `u`. A set $X$ is open in the Fortissimo Space if either `p` is contained in the complement of `X` or the complement of `X` is countable.

* We show that the Fortissimo Space is a T1 Space.
`TODO`: Prove that Fortissimo Space is T5

-/


/--Making the Fortissimo Space. A Set `X`is an open set in uncountable space if `p ∈ Xᶜ ` or `Xᶜ` is countable. In order to enforec full generality, we don't introduce the fact that Fortissimo Space is not countable.-/
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

/-! Here we prove the fact that Fortissimo Space is a T1 Space. 
Proof Sketch : `p` is a particular point the Fortissimo Space , then for any 2 arbitrary distinct points, we consider 2 cases, either one of them is a `p` or both of them are not `p`. If y is `p` then consider `U = {p}ᶜ`, and ,hence `U` is an open set(`{p}` is countable) with `x ∈ U` & `y ∉ U` If x is `p`, then take U to be `{y}ᶜ` , then  `U` is an open set(`{y}` is countable) with `x ∈ U` & `y ∉ U`.
If both x and y are not p, then take `U = {p,y}ᶜ` then  `U` is an open set(p contains `{p,y}` ) with `x ∈ U` & `y ∉ U` 
 -/
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

/-!It is also a T5 Space, as it is a T1 Space and for any two seperated sets `A` and `B` if neither contains `p`, then they are both open and we are already done. If one of them contains P, say `A`, then `p ∉ B` and hence B is open . 
B is also closed , because if not then `Bᶜ` is not open , so this means that B contains uncountable elements, `closure B` also contains uncountable elements. But `(closure B)ᶜ` is open and `(closure B)ᶜᶜ = closure B` is uncountable, thus `(closure B)ᶜᶜ = closure B` must contain `p`. But `p ∈ A`, thus `closure B ∩ A ≠ ∅ `, which is a contradiction as A and B are seperated sets.
So, `B` and `Bᶜ` are required open sets such that `A ⊆ Bᶜ ` and `B ⊆ B`. 
-/

/--Fortissimo Space is a T5 Space-/
instance FS_T₅ : T5Space α := by

  sorry

end FortissiomoSpace
