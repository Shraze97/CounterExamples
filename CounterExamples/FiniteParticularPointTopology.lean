import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology

universe u v w
/-!
# Finite Particular Point Topology
In a universe of elements of Type u, we define a Topological Space  on u, called the Finite Particular Point Topology. This Topology is defined by taking a particular point p ∈ u and defining the open sets to be those that contain p or are empty.

* Here we have proved the fact that Finite Particular Point Topology is a TO Space[Kolmogorov Space]

* We have also proved the Fact that it is not a T1 Space.
 -/

/--Making the Finite Particular Point Topology-/
def FiniteParticularPointTopology_mk{α : Type u}[Fintype α ](p : α ) : TopologicalSpace α  where
  IsOpen X:= p ∈ X ∨ X = ∅
  isOpen_univ :=
    by
      simp only [mem_univ, univ_eq_empty_iff, true_or]
  isOpen_inter := by
    intro s t hs ht
    simp only [mem_inter_iff]
    cases hs with
      | inl hp =>
        cases ht with
          | inl hq =>
            left
            exact ⟨hp,hq⟩
          | inr hq =>
            right
            rw [hq]
            simp only [inter_empty]
      | inr hp =>
        right
        rw [hp]
        simp only [empty_inter]
  isOpen_sUnion := by
    intro S hS
    by_cases hSempty : ⋃₀S = ∅
    · simp only [hSempty, mem_empty_iff_false, or_true]
    · simp only [mem_sUnion,hSempty,exists_prop,or_false]
      push_neg at hSempty
      let x := hSempty.some
      have hx : x ∈ ⋃₀S := Set.Nonempty.some_mem hSempty
      rw[Set.mem_sUnion] at hx
      cases hx with
        | intro t ht =>
          use t
          have hnt : t.Nonempty := Set.nonempty_of_mem ht.2
          simp at hS
          exact ⟨ht.1, Or.resolve_right (hS t ht.1) (Set.nonempty_iff_ne_empty.mp hnt)⟩


section FiniteParticularPointTopology
variable (α : Type u)[f : Fintype α][t :TopologicalSpace α](p : α)(topology_eq : t = FiniteParticularPointTopology_mk p)

/--An open set in FPT either contains p or is empty-/
theorem FPT_open_iff {X : Set α} : IsOpen X ↔ p ∈ X ∨ X = ∅ := by
  rw [topology_eq]
  exact Iff.rfl

/-! Here we prove that Finite Particular Point Topology is a T0 Space.
Proof Sketch : For any `x,y ∈ τ`, We take 2 cases either `(x = p) ∨ (y = p)` or both of them are not `p`. In the first case, consider wlog `x = p` then the set `S : {p}` is open as `p ∈ S`. Also, `x ∈ S` but `y ∉ S`. And hence we are done.
In the case take the set `S : {p,x}`, the S is open s `p ∈ S`. Also, `x ∈ S` but `y ∉ S`. And hence we are done.

-/
/--FPT is T0-/
instance FPT_T₀ : T0Space α := by
    rw[t0Space_iff_inseparable]
    intro x y hxy
    by_contra ha
    by_cases h : (x = p) ∨ (y = p);
    · wlog hp : x = p
      apply this α p
      apply topology_eq
      have hinsep : Inseparable y x:= Inseparable.symm hxy
      apply hinsep
      apply Ne.symm ha
      exact h.symm
      exact Or.resolve_left h hp
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p}
      have hsdef : s = {p} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p topology_eq ]
        left
        exact rfl
      apply ha
      have hy : y ∈ s := by
        rwa[←hxy s hs]
      rw [hsdef] at hy
      simp only [mem_singleton_iff] at hy
      rw[hy,hp]
    · push_neg at h
      apply ha
      rw[inseparable_iff_forall_open] at hxy
      let s : Set α := {p,x}
      have hsdef : s = {p,x} := by rfl
      have hs : IsOpen s := by
        rw[FPT_open_iff α p topology_eq]
        left
        simp only [mem_singleton_iff, mem_insert_iff, true_or]
      have hx : x ∈ s := by
        simp only [mem_singleton_iff, mem_insert_iff]
        right
        trivial
      have hy : y ∈ s := by
        rwa[← hxy s hs ]
      rw [hsdef] at hy
      simp only [mem_singleton_iff, mem_insert_iff] at hy
      exact (Or.resolve_left hy h.2).symm

/-! Here we first introduce the fact that the no. of elements in the space is greater than 2 (otherwise it's a Sierpinski Space) -/
variable (hn : Fintype.card α > 2 )

/--FPT is non-trivial , as it contains more than 2 elements-/
instance Nontrivial_α : Nontrivial α := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  linarith
/-! Here we prove that Finite Particular Point Topology is not a  T1 Space.
Proof Sketch : In order to prove that it is not T1, one needs to show that there exists distinct elements `a,b ∈ τ`, such that for all open sets  `U ∈ τ`,if `a ∈ U`, then `b ∈ U`, So, we consider `a ≠  p` and `b = p`  be our 2 elements. The any open set `U : Open` , , if `a ∈ U`, then by definition `b ∈ U`.  -/

/--FPT is not T₁-/
theorem FPT_not_T₁ : ¬ T1Space α := by
  rw[t1Space_iff_exists_open]
  rw[Pairwise]
  push_neg
  have heq : ∃ (a : α) (b: α) (c: α ), a ≠ b ∧ a ≠ c ∧ b ≠ c := Fintype.two_lt_card_iff.mp hn
  match heq with
  | ⟨a,b,c,hab,hbc,hca⟩ =>
    by_cases h : a = p
    · rw[h] at hab
      use b
      use p
      constructor
      exact hab.symm
      intros U hU hbU
      rw[FPT_open_iff α p topology_eq] at hU
      have hnU : U ≠ ∅ := by
        intro hUempty
        rw[hUempty] at hbU
        exact hbU
      exact Or.resolve_right hU hnU
    · use a
      use p
      constructor
      exact h
      intros U hU haU
      rw[FPT_open_iff α p topology_eq] at hU
      have hnU : U ≠ ∅ := by
        intro hUempty
        rw[hUempty] at haU
        exact haU
      exact Or.resolve_right hU hnU

end FiniteParticularPointTopology
