
import CounterExamples.DeletedIntegerTopology
import CounterExamples.FiniteParticularPointTopology     
import CounterExamples.FortissimoSpace
import CounterExamples.HalfDiscTopology
import CounterExamples.IrrationalSlopeTopology
import CounterExamples.UncountableFiniteComplementSpace

/-!
# Counter Examples in Topology

Here I have these Topological Spaces under development
* Deleted Integer Topology
* Finite Particular Point Topology
* Fortissimo Space
* Half Disc Topology
* Irrational Slope Topology
* Uncountable Finite Complement Space

So, the sources that I have used to formalize these spaces are as follows:
* [Counterexamples in Topology](https://en.wikipedia.org/wiki/Counterexamples_in_Topology)
* [N. Bourbaki, *General Topology*][bourbaki1966]

The main function of this project is to make Counter Examples in Topology, So, given a conjecture in topology, the computer can specialize any of these counter-examples for this conjecture and give a quick disproof of the conjecture. 
Here, I have specifically focussed on implementing the counter examples in topology baased on these seperation axioms :-
* `T0 axiom`: If `a,b ∈ X`; there exist an open set `O ∈ τ ` such that `a ∈ O` and `b ∉ O`, or `b ∈ O` and `a ∉ 0`
* `T1 axiom` : If `a,b ∈ X` , there exists open sets `U` and `V ` st. `x ∈ U`,`y ∈ V` and `x ∉ V`,`y ∉ U`.
* `T2 axiom` : If `a,b ∈ X` , there exists open sets `U` and `V ` st. `x ∈ U`,`y ∈ V` and `U ∩ V = ∅`. 
* `T2.5 axiom` : If `a,b ∈ X` , there exists open sets `U` and `V ` st. `x ∈ U`,`y ∈ V` and `closure U ∩ closure V = ∅`.
* `T3 axiom`: If `A` is a closed set and `b` is a point not in A, there exists open sets `U` and `V ` st. `A ⊆ U`,`b ∈ V` and `U ∩ V = ∅`.
* `T4 axiom`: If `A` and `B` are disjoint sets then there exists open sets `U` and `V ` st. `A ⊆ U`,`B ⊆ V` and `U ∩ V = ∅`.
* `T5 axiom` : If `A` and `B` are seperated sets i.e `closure A ∩ B = ∅ ` and `A ∩ closure B = ∅ `, then there exists open sets `U` and `V ` st. `A ⊆ U`,`B ⊆ V` and `U ∩ V = ∅`. In Bourbaki and lean's definition it also inherits the `T1` Space. 


So, in order to distinguish these Seperation Axioms , the plan of the project is to formalize these Topological Spaces :-
* `Deleted Integer Topology` : A Topological Space which is not `T0`
* `Finite Particular Point Topology` :  A Topological Space which is not `T1` but is `T0`.
* `Uncountable Finite Complement Topology` : A Topological Space which is not `T2` but is `T1`.
* `Irrational Slope Topology` : A Topological Space which is `T2.5` but not `T2`.
* `Half Disc Topology` : A Topological Space which is `T3` but not `T2.5` 
* `Fortissimo Space` : A Topological Space which is `T5`.

# Navigation
To browse the code, click on the navigation tab
-/

