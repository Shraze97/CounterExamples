import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib
set_option autoImplicit true


noncomputable section

open Function Set Filter Topology TopologicalSpace
/-!
# Deleted Integer Space
Deleted Integer Space is a Topological Space generated given on a structure `DeletedIntegerSpace(ℝ+)` where the elements are positive Real Numbers with deleted Integers i.e we remove all the integer points from the Space.
Now, we construct a partition`DIT_Partition` on this topology which is set of `modified_Ioo : Set ℝ+`.
`modified_Ioo` contains all the elements of `ℝ+` that lie between two consecutive integers.
We then construct a Topology on `ℝ+` by considering that these elements are contained in those open sets .
We also construct `DIT_indexed_partition` for future use. 
 -/


universe u v w
/--Structure Describing the Deleted Integer Space-/
structure DeletedIntegerSpace where
  x : ℝ
  hn : x > 0
  hx : ∀ y : ℕ , x ≠ y

/--Notation for `ℝ+`-/
notation "ℝ+" => DeletedIntegerSpace

/--sets in ℝ+  which contain all the points between `b` and `b + 1`.-/
@[inline]
def modified_Ioo(b : ℕ) : Set ℝ+ :=
  {a : ℝ+ | a.1 ∈ Set.Ioo (b : ℝ) (b + 1 : ℝ )  }

/-! 
# Partition : Setoid.Partition
A Partiition is a set of sets such that
 * all elements of the partition are disjoint and non-empty 
 * every element of the Space is contained in a unique element of the partition.
So, the union of all the sets in the partition is the whole space. 
-/


/--Partition of sets in ℝ+ on which we develop the partition topology-/
def DIT_partition : Set (Set ℝ+) :=
  {S | ∃ (a : ℕ) , S = modified_Ioo a}

/--Creating an indexing function which gives us elements of the partition defined above-/
def DIT_indexed_partition : ℕ → Set ℝ+ :=
  λ a => modified_Ioo a

/--Auxiliary lemma which shows the range of the indexing function is DIT_partition -/
lemma DIT_partition_equiv_indexed_partition : DIT_partition = Set.range DIT_indexed_partition := by
  ext S
  constructor
  · intro hS
    simp only [mem_range,DIT_indexed_partition]
    rw[DIT_partition,mem_setOf_eq] at hS
    match hS with
    | ⟨a,ha⟩ =>
    use a
    rw[ha]
  · intro hS
    simp only [mem_range,DIT_indexed_partition] at hS
    rw[DIT_partition,mem_setOf_eq]
    match hS with
    | ⟨a,ha⟩ =>
    use a
    rw[ha]


/--Lemma showing the fact that if 0.5 is added to a natural number then it is not equal to another natural number. This is used in producing an element of ℝ+-/
lemma pointfive_plus_x(x : ℕ) : ∀ y : ℕ , ((x: ℝ ) + 0.5 ) ≠ (y : ℝ) := by
  norm_num
  field_simp
  intros y h
  have : 1 = ((y : ℝ) - (x : ℝ)) * 2 := by
    linarith
  have b : ((y : ℝ) - (x : ℝ)) * 2 > 0 := by linarith
  apply Nat.not_even_one
  norm_cast at this
  rw[Nat.even_iff]
  zify
  rw[this]
  simp only [Int.mul_emod_left]

/--Lemma showing the fact that if 0.25 is added to a natural number then it is not equal to another natural number. This is used in producing an element of ℝ+-/
lemma twentyfive_plus_x(x : ℕ) : ∀ y : ℕ , ((x : ℝ ) + 0.25) ≠ (y : ℝ) := by
  norm_num
  field_simp
  intros y h
  have : 1 = ((y : ℝ) - (x : ℝ)) * 2*2 := by
    linarith
  apply Nat.not_even_one
  norm_cast at this
  rw[Nat.even_iff]
  zify
  rw[this]
  simp only [Int.mul_emod_left]

/--Lemma used in producing an element of ℝ+-/
lemma x_plus_one_gt_zero(x : ℕ) : (x : ℝ) + 0.5 >  0 := by
  norm_num
  field_simp
  apply mul_pos
  have hx : (x*2 : ℝ) ≥  0 := by
    apply mul_nonneg
    norm_num
    norm_num
  linarith
  norm_num


lemma floor_cast_aux_2(r : ℝ+): Int.toNat ⌊r.x⌋ = Int.floor (r.x) := by
  rw[Int.toNat_of_nonneg]
  rw[Int.floor_nonneg]
  apply le_of_lt
  apply r.hn


lemma floor_cast_aux(r: ℝ+): @Nat.cast ℝ Real.natCast  (Int.toNat (Int.floor (r.x)))  =  Int.floor (r.x):= by
  norm_cast
  rw[floor_cast_aux_2 r]


/--Theorem Proving the fact that DIT_partition is a partition-/
theorem DIT_partition_is_partition : Setoid.IsPartition DIT_partition  := by
  rw[Setoid.IsPartition]
  constructor
  · rw[DIT_partition]
    simp only [mem_setOf_eq, not_exists]
    intro x
    apply Ne.symm
    rw[← Set.nonempty_iff_ne_empty,nonempty_def]
    set a : ℝ+ :=  {x := (x : ℝ)  + 0.5, hn := x_plus_one_gt_zero x , hx := pointfive_plus_x x} with ha
    use a
    rw[modified_Ioo]
    rw[mem_setOf_eq,Set.Ioo,mem_setOf_eq]
    constructor
    rw[ha]
    repeat (first | simp | norm_num)
  · intro r
    apply ExistsUnique.intro (modified_Ioo (Int.floor (r.x)).toNat)
    apply ExistsUnique.intro
    rw[modified_Ioo]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le, add_le_iff_nonpos_right, mem_Ioo,
      mem_setOf_eq]
    constructor
    norm_num
    rw[floor_cast_aux r,lt_iff_le_and_ne]
    constructor
    apply Int.floor_le
    intro ken
    apply r.hx
    rw[← ken,← floor_cast_aux r]
    rw[floor_cast_aux r]
    simp only [Int.lt_floor_add_one]
    swap
    have he' : modified_Ioo (Int.toNat ⌊r.x⌋) ∈ DIT_partition := by
      rw[DIT_partition]
      simp only [mem_setOf_eq]
      use Int.toNat ⌊r.x⌋
    apply he'
    intros he _
    simp only
    intros y ha
    match ha with
    | ⟨hy,hxa,hab ⟩ =>
    simp only at hxa
    simp only [implies_true] at hab
    rw[DIT_partition] at hy
    simp only [mem_setOf_eq] at hy
    match hy with
    |⟨ a, hay⟩ =>
    rw[hay,modified_Ioo] at hxa
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le, add_le_iff_nonpos_right, mem_Ioo,
      mem_setOf_eq] at hxa
    norm_cast at hxa
    have hra : Int.toNat (Int.floor (r.x)) = a := by
      zify
      rw[floor_cast_aux_2 r]
      rw[Int.floor_eq_iff]
      norm_cast
      constructor
      exact le_of_lt hxa.1
      exact hxa.2
    rw[hra]
    assumption

/--Making a Deleted Integer Topology as a Topological Space in ℝ+, generated from DIT_Partition i.e all the open sets are generated from union of sets in DIT and finite intersection of sets in DIT -/
def DeletedIntegerTopology_mk : TopologicalSpace ℝ+ :=
  TopologicalSpace.generateFrom (DIT_partition)


lemma aux_insertion(α : Type u)(w : Set α)(y : Set α)(a : Set (Set α ))(hmain : {y,w} ⊆ a): @Subset (Set (Set α)) instHasSubsetSet {w} (a) := by
    trans
    swap
    exact hmain
    simp only [mem_singleton_iff, subset_insert]

lemma aux_insertion_adv(α : Type u)(w : Set α)(y : Set α)(z : Set α )(a : Set (Set α ))(hmain : {w,y,z} ⊆  a): @Subset (Set (Set α)) instHasSubsetSet {w} ( a) := by
  trans
  swap
  exact hmain
  simp only [mem_singleton_iff, mem_insert_iff, singleton_subset_iff, true_or]

/--Permutation of certain elements in Set (Set α)-/
lemma permutation_elements(α : Type u)(w : Set α)(y : Set α)(z : Set α): {w,y,z} = @insert (Set α) (Set (Set α)) instInsertSet y {w, z} ∧ {w,y,z} = @insert (Set α) (Set (Set α)) instInsertSet z {w, y} ∧ {w,y,z} = @insert (Set α) (Set (Set α)) instInsertSet z {y, w}:= by
  constructor
  rw[Set.insert_comm]
  constructor
  repeat rw[Set.insert_eq]
  rw [Set.union_comm {y} {z}]
  rw[← Set.union_assoc]
  rw[Set.union_comm {w} {z}]
  rw[Set.union_assoc]
  repeat rw[Set.insert_eq]
  rw [Set.union_comm {y} {z}]
  rw[← Set.union_assoc]
  rw[Set.union_comm {w} {z}]
  rw[Set.union_assoc]
  rw[Set.union_comm {w} {y}]

/--Distinct elements of the partition are disjoint-/
lemma IsPartition_intersection (α : Type u)(x : Set α)(y : Set α )(c : Set (Set α))(hc : Setoid.IsPartition c )(hx : x ∈ c)(hy : y ∈ c)(hxy : x ≠ y) : x ∩ y = ∅  := by
  rw[← Set.disjoint_iff_inter_eq_empty]
  have hpdxy : Set.PairwiseDisjoint c id := Setoid.IsPartition.pairwiseDisjoint hc
  rw[Set.PairwiseDisjoint] at hpdxy
  specialize hpdxy hx hy hxy
  rw[onFun_apply] at hpdxy
  simp only [id_eq] at hpdxy
  assumption

/--The  Basis of the Toopological Space, we will prove later that this indeed becomes the basis of DIT when c is DIT_Partition-/
def TopBasis(c : Set (Set α))(hc : Setoid.IsPartition c ) : Set (Set α) := c ∪ {univ} ∪ {∅} 

section DeletedIntegerTopology

variable [t : TopologicalSpace ℝ+](topology_eq : t = DeletedIntegerTopology_mk)
/-!
# Plan to Formalize that DIT is not T0
* First we Formalize the fact that the basis of DIT is the TopBasis specialised for the DIT_Partition i.e the basis of DIT is the union of DIT_partition, the empty set and the universal set.
* Then for any 2 points `x,y` in the same `P := modified_Ioo`, every open set containing `x` will contain `y` because the basic set `P` will be contained in every open set `U` which contains `x`. This is because `P` and `univ` are the only basic open sets which contain `x`.
Then we are done
-/

/--Lemma stating the fact that in a partition (with 2 elements), the finite intersection of elements is member of TopBasis -/
lemma Card_case_2 (α : Type u)[DECα : DecidableEq (Set α)](c : Set (Set α))(hc : Setoid.IsPartition c )(S : Set α)(x : Set (Set α) )(hxfin : @Set.Finite (Set α) x)(hrr : @Finset.card (Set α) (Finite.toFinset hxfin) = 2)(hxc : x ⊆  c)(hx : ⋂₀ x = S) : S ∈ c ∪ {univ} ∪ {∅}:= by
  rw[Finset.card_eq_two] at hrr
  match hrr with
  | ⟨w,y ,hyw, hy ⟩ =>
  haveI hfx: Fintype x := Set.Finite.fintype hxfin
  simp only [toFinite_toFinset] at hy
  have h : @insert (Set α) (Finset (Set α)) Finset.instInsertFinset w {y} = toFinset {w,y}:= by simp only [Finset.mem_singleton,
    mem_singleton_iff, toFinset_insert, toFinset_singleton]
  have hdoublef : Set.Finite (@insert (Set α) (Set (Set α)) instInsertSet w {y}) := by simp only [mem_singleton_iff,
    finite_singleton, Finite.insert]
  rw[h] at hy
  rw[← Set.Finite.toFinset_eq_toFinset hxfin, ← Set.Finite.toFinset_eq_toFinset hdoublef,Set.Finite.toFinset_inj] at hy
  rw[hy] at  hxc
  have hxysame : @insert (Set α) (Set (Set α)) instInsertSet w {y} = @insert (Set α) (Set (Set α)) instInsertSet y {w} := Set.pair_comm w y
  rw[Set.insert_subset_iff,Set.singleton_subset_iff] at hxc
  rw[hy] at hx
  simp only [mem_singleton_iff, sInter_insert, sInter_singleton] at hx
  rw[← hx]
  right
  simp only [mem_singleton_iff]
  apply IsPartition_intersection α w y c hc hxc.1 hxc.2 hyw


/--Lemma stating the fact that in a partition(general case) the finite intersection of elements is contained in the TopBasis of the Partition-/
lemma finite_intersection_of_partition(α : Type u) (c : Set (Set α))(hc : Setoid.IsPartition c )(hcnon : c.Nontrivial) : c ∪{univ}∪ {∅}  = ((fun (f: Set (Set α)) => ⋂₀ f) '' {f | Set.Finite f ∧ f ⊆ (c ) }) := by
  ext S
  constructor
  intro hSc
  rw[Set.mem_image]
  by_cases hSnonempty : S ≠ ∅
  by_cases hSnonuniv : S ≠ univ
  set f : Set (Set α) := {S} with hf
  use f
  simp only [mem_setOf_eq, finite_singleton, singleton_subset_iff, true_and, sInter_singleton, and_true]
  rw [union_singleton, mem_insert_iff] at hSc
  apply Or.resolve_right (Or.resolve_left hSc hSnonempty) hSnonuniv
  push_neg at hSnonuniv
  use ∅
  simp only [mem_setOf_eq, finite_empty, empty_subset, and_self, sInter_empty, hSnonuniv]
  push_neg at hSnonempty
  rw[Set.nontrivial_iff_pair_subset] at hcnon
  simp at hcnon
  match hcnon with
  | ⟨x,y,hxy,hxyhab⟩ =>
    set a : Set (Set α) := {x,y} with ha
    use a
    simp only [mem_singleton_iff, mem_setOf_eq, finite_singleton, Finite.insert, true_and, sInter_insert,
      sInter_singleton]
    constructor
    rw[← ha]
    trans
    exact hxyhab
    rfl
    rw[hSnonempty,← Set.disjoint_iff_inter_eq_empty]
    have lem : c.PairwiseDisjoint id:= Setoid.IsPartition.pairwiseDisjoint hc
    rw[Set.PairwiseDisjoint,Set.Pairwise] at lem
    have hx : (x ∈ c)∧ (y ∈ c) := by
      constructor
      all_goals rw[ha] at hxyhab
      all_goals rw[←singleton_subset_iff]
      all_goals trans
      any_goals exact hxyhab
      simp only [mem_singleton_iff, singleton_subset_iff, mem_insert_iff, true_or]
      simp only [mem_singleton_iff, subset_insert]
    specialize lem hx.1 hx.2 hxy
    rw[onFun_apply] at lem
    simp only [id_eq] at lem
    exact lem
  intro hS
  simp at hS
  match hS with
  |⟨x, ⟨⟨hxfin,hxc⟩ ,hx⟩⟩ =>
  by_cases hnum : (Set.Finite.toFinset hxfin).card ≤ 2
  · simp only at hnum
    have h : Finset.card (Finite.toFinset hxfin) = 2 ∨ Finset.card (Finite.toFinset hxfin) = 1 ∨ Finset.card (Finite.toFinset hxfin) = 0:= by
      interval_cases Finset.card (Finite.toFinset hxfin)
      all_goals{simp}
    cases h with
    | inl hrr =>
      haveI Decidable_Setα  : DecidableEq (Set α) := Classical.decEq (Set α)
      apply Card_case_2 α c hc S x hxfin hrr hxc hx
    | inr hlr =>
    cases hlr with
    | inl hl =>
      rw[Finset.card_eq_one] at hl
      match hl with
      |⟨y,hy⟩ =>
      rw[← Set.Finite.toFinset_singleton,Set.Finite.toFinset_inj] at hy
      rw[hy] at hx hxc
      simp only [sInter_singleton, singleton_subset_iff] at hx hxc
      rw[←hx]
      left
      left
      assumption
    | inr hr =>
      simp only [Finset.card_eq_zero, Finite.toFinset_eq_empty] at hr
      rw[hr] at hx
      simp at hx
      rw[← hx]
      simp only [union_singleton, mem_insert_iff, univ_eq_empty_iff, true_or, or_true]
  push_neg at hnum
  rw[Finset.two_lt_card] at hnum
  match hnum with
  | ⟨y,hy,z,hz,w,hw,hyz,hyw,hzw⟩ =>
  simp only [union_singleton, mem_insert_iff]
  rw[Set.Finite.mem_toFinset] at hy hz hw
  have hwyz : {w,y,z} ⊆ x := by
    rw[Set.insert_subset_iff,Set.insert_subset_iff,Set.singleton_subset_iff]
    exact ⟨hw,hy,hz⟩
  have hwyzc : {w,y,z} ⊆ c := subset_trans hwyz hxc
  have hwc : {w} ⊆  c := aux_insertion_adv α w y z c hwyzc
  have hyc : {y} ⊆  c := by
    apply aux_insertion_adv α y w z c
    rwa[← (permutation_elements α w y z).1]
  have hzc : {z} ⊆  c := by
    apply aux_insertion_adv α z w y c
    rwa[← ((permutation_elements α w y z).2).1]
  simp only [singleton_subset_iff, mem_insert_iff] at hyc hwc hzc
  have hwc' : {w,z} ⊆ x := by
    rw[Set.insert_subset_iff,Set.singleton_subset_iff]
    exact ⟨hw,hz⟩
  have hsinter_sub : ⋂₀ x ⊆ ⋂₀ {w,z} := Set.sInter_subset_sInter hwc'
  have hwc_empty : ⋂₀ {w,z} = ∅ := by
    simp only [mem_singleton_iff, sInter_insert, sInter_singleton]
    apply IsPartition_intersection α w z c hc hwc hzc (Ne.symm hzw)
  rw[hwc_empty] at hsinter_sub
  rw[hx] at hsinter_sub
  simp only [subset_empty_iff] at hsinter_sub
  simp only [hsinter_sub, true_or]


/--Theorem stating the fact that DIT is non_trivial,i,e it contains more than 2 elements, this is required for the fact that DIT_basis contains the ∅ set because if not, the basis of the topology will not contain the empty set, a contradiction-/
theorem DIT_nontrivial : DIT_partition.Nontrivial := by
  rw[Set.Nontrivial]
  set a1 : Set ℝ+ := modified_Ioo 1 with ha1
  set a2 : Set ℝ+ := modified_Ioo 3 with ha2
  use a1
  constructor
  rw[DIT_partition]
  simp only [mem_setOf_eq]
  use 1
  use a2
  constructor
  simp only [mem_setOf_eq]
  use 3
  rw[ha1,ha2]
  by_contra H
  set a : ℝ+ := {x := (3: ℝ) + 0.5, hn := by norm_num, hx := pointfive_plus_x 3} with ha
  have h : a ∈ a2 := by
    rw[ha2]
    simp only [mem_setOf_eq,modified_Ioo,Nat.cast_ofNat, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le,
      add_le_iff_nonpos_right, mem_Ioo, add_lt_add_iff_left]
    norm_num
  rw[ha2,←H] at h
  simp only [mem_setOf_eq,modified_Ioo] at h
  simp only [Nat.cast_ofNat, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, not_true, ge_iff_le,
    add_le_iff_nonpos_right, mem_Ioo, add_lt_add_iff_left] at h
  norm_num at h

/--The base of the Deleted Integer Topology-/
@[inline]
def DIT_basis := TopBasis DIT_partition DIT_partition_is_partition 

/--Theorem to prove that Topological Basis of DIT is DIT_Basis -/
theorem DIT.TopologicalBasis : TopologicalSpace.IsTopologicalBasis DIT_basis:= by
  rw[DIT_basis]
  rw[TopBasis]
  rw[DeletedIntegerTopology_mk] at topology_eq
  rw[finite_intersection_of_partition ℝ+ (DIT_partition) (DIT_partition_is_partition) (DIT_nontrivial) ]
  apply TopologicalSpace.isTopologicalBasis_of_subbasis topology_eq

/--Auxilary Theorem to prove the fact that DIT is not T0-/
lemma DIT_not_T0_aux(x1 : ℝ+)(x2 : ℝ+)(S : Set ℝ+)(a : Set ℝ+)(ha : a = modified_Ioo 2)(hx1a : x1 ∈ a)(hx2a : x2 ∈ a)(hS : IsOpen S) : x1 ∈ S →  x2 ∈ S := by
  intro hSx1
  rw[TopologicalSpace.IsTopologicalBasis.isOpen_iff (DIT.TopologicalBasis topology_eq)] at hS
  rw[DIT_basis,TopBasis] at hS
  specialize hS x1 hSx1
  match hS with
  |⟨t1, htdit,htx1, hts⟩ =>
  by_cases h : t1 = univ
  rw[h,Set.univ_subset_iff] at hts
  rw[hts]
  simp only [mem_univ]
  have htnonempty : t1 ≠ ∅ := by
    intro hemp
    rw[hemp] at htx1
    simp only [mem_empty_iff_false] at htx1
  replace htdit : t1 ∈ DIT_partition := by
    simp only [union_singleton, mem_insert_iff] at htdit
    apply Or.resolve_left (Or.resolve_left htdit htnonempty) h
  have dita : a ∈ DIT_partition := by
    rw[DIT_partition]
    simp only [mem_setOf_eq]
    use 2
  apply Set.mem_of_subset_of_mem hts
  have hat : a = t1 := by
    by_contra hat
    have hx1ta : x1 ∈ t1 ∩ a := Set.mem_inter htx1 hx1a
    apply Set.nonempty_iff_ne_empty.mp
    apply Set.nonempty_def.mpr ⟨ x1, hx1ta⟩
    apply IsPartition_intersection ℝ+ t1 a DIT_partition DIT_partition_is_partition htdit dita (Ne.symm hat)
  rw[← hat]
  assumption

/--Deleted Integer Topology is not T0-/
theorem DIT_not_T0 : ¬ T0Space ℝ+ := by
  rw[t0Space_iff_inseparable]
  push_neg
  set x1 :ℝ+ := {x := (2: ℝ ) + 0.5 , hn := by norm_num, hx := by exact pointfive_plus_x 2} with hx1
  set x2 :ℝ+ := {x := (2: ℝ ) + 0.25 , hn := by norm_num, hx := by exact twentyfive_plus_x 2} with hx2
  use x1
  use x2
  rw[inseparable_iff_forall_open]
  constructor
  intros S hS
  set a : Set ℝ+ := modified_Ioo 2 with ha
  have hx1a : x1 ∈ a := by simp[modified_Ioo];norm_num
  have hx2a : x2 ∈ a := by simp[modified_Ioo];norm_num
  constructor
  apply DIT_not_T0_aux topology_eq x1 x2 S a ha hx1a hx2a hS
  apply DIT_not_T0_aux topology_eq x2 x1 S a ha hx2a hx1a hS
  rw[hx1,hx2]
  simp only [ne_eq, DeletedIntegerSpace.mk.injEq, add_right_inj]
  norm_num

end DeletedIntegerTopology
