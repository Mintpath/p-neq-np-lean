import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

open Finset

namespace PNeNp

abbrev Edge (n : ℕ) := Sym2 (Fin n)

noncomputable def allEdges (n : ℕ) : Finset (Edge n) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

def completeGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.completeGraph (Fin n)

section BooleanCircuit

inductive GateKind where
  | AND
  | OR
  | NOT
  deriving BEq, DecidableEq

structure Gate where
  kind : GateKind
  input1 : ℕ
  input2 : ℕ
  deriving BEq

structure BooleanCircuit (numInputs : ℕ) where
  gates : List Gate
  outputGate : ℕ

def BooleanCircuit.size {m : ℕ} (C : BooleanCircuit m) : ℕ :=
  m + C.gates.length

noncomputable def BooleanCircuit.eval {m : ℕ} (C : BooleanCircuit m)
    (input : Fin m → Bool) : Bool :=
  let values := C.gates.foldl (init := (List.ofFn input))
    fun acc g =>
      let v1 := acc.getD g.input1 false
      let v2 := acc.getD g.input2 false
      let result := match g.kind with
        | GateKind.AND => v1 && v2
        | GateKind.OR  => v1 || v2
        | GateKind.NOT => !v1
      acc ++ [result]
  values.getD (C.outputGate) false

def BooleanCircuit.fanOut {m : ℕ} (C : BooleanCircuit m) (i : ℕ) : ℕ :=
  C.gates.foldl (init := 0) fun acc g =>
    acc + (if g.input1 = i then 1 else 0) + (if g.input2 = i then 1 else 0)

def BooleanCircuit.isFormula {m : ℕ} (C : BooleanCircuit m) : Prop :=
  (∀ i : ℕ, i < C.gates.length + m → C.fanOut i ≤ 1) ∧
  (∀ j : ℕ, ∀ hj : j < C.gates.length,
    let g := C.gates[j]'hj
    g.input1 < m + j ∧ g.input2 < m + j)

end BooleanCircuit

section VertexDegree

def vertexDegreeIn (n : ℕ) (edges : Finset (Edge n)) (v : Fin n) : ℕ :=
  (edges.filter fun e => v ∈ e).card

end VertexDegree

section HamiltonianCycle

noncomputable def edgeSetToGraph (n : ℕ) (edges : Finset (Edge n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (Sym2.mk (u, v)) ∈ edges
  symm := by
    intro u v ⟨hne, hmem⟩
    exact ⟨hne.symm, Sym2.eq_swap ▸ hmem⟩
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

open Classical in
def IsConnectedEdgeSet (n : ℕ) (edges : Finset (Edge n)) : Prop :=
  (edgeSetToGraph n edges).Connected

def IsIncidentConnected (n : ℕ) (edges : Finset (Edge n)) : Prop :=
  ∀ v w : Fin n,
    (∃ e ∈ edges, v ∈ e) → (∃ e ∈ edges, w ∈ e) →
    (edgeSetToGraph n edges).Reachable v w

structure IsHamCycle (n : ℕ) (edges : Finset (Edge n)) : Prop where
  twoRegular : ∀ v : Fin n, vertexDegreeIn n edges v = 2
  connected : IsConnectedEdgeSet n edges
  noLoops : ∀ e ∈ edges, ¬ e.IsDiag
  spanning : ∀ v : Fin n, ∃ e ∈ edges, v ∈ e

end HamiltonianCycle

section HAM

open Classical in
noncomputable def HAM (n : ℕ) (x : Edge n → Bool) : Bool :=
  if IsHamCycle n (Finset.univ.filter fun e => x e = true) then true else false

theorem HAM_spec (n : ℕ) (x : Edge n → Bool) :
    HAM n x = true ↔ IsHamCycle n (Finset.univ.filter fun e => x e = true) := by
  unfold HAM
  split <;> simp_all

def CircuitDecidesHAM {m : ℕ} (C : BooleanCircuit m)
    (toInput : Finset (Edge n) → (Fin m → Bool)) : Prop :=
  ∀ G : Finset (Edge n), C.eval (toInput G) = true ↔ IsHamCycle n G

end HAM

section Frontier

structure Frontier (n : ℕ) where
  leftEdges : Finset (Edge n)
  rightEdges : Finset (Edge n)
  partition : leftEdges ∪ rightEdges = allEdges n
  disjoint : Disjoint leftEdges rightEdges

def Frontier.isBalanced {n : ℕ} (S : Frontier n) : Prop :=
  S.leftEdges.card ≥ 1 ∧ S.rightEdges.card ≥ 1

def Frontier.isInterior {n : ℕ} (S : Frontier n) : Prop :=
  S.isBalanced

def Frontier.swap {n : ℕ} (S : Frontier n) : Frontier n where
  leftEdges := S.rightEdges
  rightEdges := S.leftEdges
  partition := by rw [Finset.union_comm]; exact S.partition
  disjoint := S.disjoint.symm

@[simp] lemma Frontier.swap_leftEdges {n : ℕ} (S : Frontier n) :
    S.swap.leftEdges = S.rightEdges := rfl

@[simp] lemma Frontier.swap_rightEdges {n : ℕ} (S : Frontier n) :
    S.swap.rightEdges = S.leftEdges := rfl

end Frontier

section Boundary

variable {n : ℕ}

noncomputable def boundaryVertices (S : Frontier n) : Finset (Fin n) :=
  Finset.univ.filter fun v =>
    (∃ e ∈ S.leftEdges, v ∈ e) ∧ (∃ e ∈ S.rightEdges, v ∈ e)

end Boundary

section LeftRight

variable {n : ℕ}

def leftSubgraph (S : Frontier n) (H : Finset (Edge n)) : Finset (Edge n) :=
  H ∩ S.leftEdges

def rightSubgraph (S : Frontier n) (H : Finset (Edge n)) : Finset (Edge n) :=
  H ∩ S.rightEdges

noncomputable def leftDegreeAt (S : Frontier n) (H : Finset (Edge n)) (v : Fin n) : ℕ :=
  vertexDegreeIn n (leftSubgraph S H) v

noncomputable def rightDegreeAt (S : Frontier n) (H : Finset (Edge n)) (v : Fin n) : ℕ :=
  vertexDegreeIn n (rightSubgraph S H) v

@[simp] lemma leftSubgraph_swap (S : Frontier n) (H : Finset (Edge n)) :
    leftSubgraph S.swap H = rightSubgraph S H := by
  unfold leftSubgraph rightSubgraph; simp

@[simp] lemma rightSubgraph_swap (S : Frontier n) (H : Finset (Edge n)) :
    rightSubgraph S.swap H = leftSubgraph S H := by
  unfold leftSubgraph rightSubgraph; simp

theorem boundaryVertices_swap (S : Frontier n) :
    boundaryVertices S.swap = boundaryVertices S := by
  unfold boundaryVertices Frontier.swap
  ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

end LeftRight

end PNeNp
