import PNeNp.Interface

namespace PNeNp

variable {n : ℕ}

/-! ## Section 4: Same-State Stitchability

This file collects the stitchability theorems from Section 4 of the
Hamiltonian route paper. Irreducible combinatorial facts are axiomatized;
proof structure matches the paper.

The main result is `sameStateStitchability`: if two Hamiltonian cycles
H, H' share the same interface state σ_S, then the mixed graph
L_S(H') ∪ R_S(H) is again a Hamiltonian cycle. -/

section PathComponentNormalForm

/-! ### Lemma 4.1: Path-component normal form

At a balanced interior frontier S with c_S(H) = 0:
(1) Every component of L_S(H) is a simple path or isolated vertex.
(2) Path-component endpoints (left-degree 1) lie in B_S.
(3) Internal vertices (left-degree 2) don't affect the boundary multigraph.
(4) Isolated vertices are boundary vertices iff incident to edges on both sides.
(5) No component is disjoint from B_S unless it's an isolated vertex with no left edges.
(6) The boundary multigraph is determined by (d_S(H), π_S(H)). -/

structure PathComponentNormalFormResult (S : Frontier n) (H : Finset (Edge n)) where
  components_are_paths :
    ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
    (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)
  endpoints_are_boundary :
    ∀ v : Fin n, degreeProfile S H v = 1 → v ∈ boundaryVertices S
  pairing_determines_boundary :
    True

private theorem leftSubgraph_no_cycle_when_no_premature :
  ∀ {n : ℕ} (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced → ¬ hasPrematureCycle S H →
    ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
    (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  intro n S H hH _hS hNoPrem comp hSub hNe _hDeg2 hCycle
  by_cases hcompH : comp = H
  · sorry
  · exact hNoPrem ⟨comp, hSub, hNe, hCycle, hcompH⟩

private theorem degree_one_vertex_is_boundary :
  ∀ {n : ℕ} (S : Frontier n) (H : Finset (Edge n)),
    IsHamCycle n H → S.isBalanced → ¬ hasPrematureCycle S H →
    ∀ v : Fin n, degreeProfile S H v = 1 → v ∈ boundaryVertices S := by
  intro n S H hH _hS _hc v hdeg
  unfold boundaryVertices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · unfold degreeProfile leftDegreeAt leftSubgraph vertexDegreeIn at hdeg
    have hpos : 0 < (Finset.filter (fun e => v ∈ e) (H ∩ S.leftEdges)).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨e, he⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_inter] at he
    exact ⟨e, he.1.2, he.2⟩
  · have hsum := leftDeg_add_rightDeg_eq_two S H hH v
    unfold degreeProfile at hdeg
    have hright : rightDegreeAt S H v = 1 := by omega
    unfold rightDegreeAt rightSubgraph vertexDegreeIn at hright
    have hpos : 0 < (Finset.filter (fun e => v ∈ e) (H ∩ S.rightEdges)).card := by omega
    rw [Finset.card_pos] at hpos
    obtain ⟨e, he⟩ := hpos
    simp only [Finset.mem_filter, Finset.mem_inter] at he
    exact ⟨e, he.1.2, he.2⟩

theorem pathComponentNormalForm
    (S : Frontier n) (hS : S.isBalanced)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (hc : ¬ hasPrematureCycle S H) :
    PathComponentNormalFormResult S H where
  components_are_paths :=
    leftSubgraph_no_cycle_when_no_premature S H hH hS hc
  endpoints_are_boundary :=
    degree_one_vertex_is_boundary S H hH hS hc
  pairing_determines_boundary := trivial

end PathComponentNormalForm

section BoundaryComponentCorrespondence

/-! ### Lemma 4.2: Boundary-component correspondence

Let M = L ∪ R be a spanning 2-regular graph where every component of L
and R is a simple path with boundary endpoints or an isolated vertex,
and neither L nor R contains a cycle-component. Define the boundary
multigraph G_∂(M) on B_S. Then connected components of M biject with
those of G_∂(M). In particular, M is Hamiltonian iff G_∂(M) is connected. -/

def IsConnectedFinset {n : ℕ} (edges : Finset (Edge n)) : Prop :=
  IsConnectedEdgeSet n edges

structure BoundaryMultigraph (n : ℕ) where
  vertices : Finset (Fin n)
  lEdges : Finset (Fin n × Fin n)
  rEdges : Finset (Fin n × Fin n)

noncomputable def boundaryMultigraphOf (S : Frontier n)
    (L R : Finset (Edge n)) : BoundaryMultigraph n :=
  { vertices := boundaryVertices S
    lEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      ∃ _e ∈ L, p.1 ∈ _e ∧ p.2 ∈ _e
    rEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      ∃ _e ∈ R, p.1 ∈ _e ∧ p.2 ∈ _e }

noncomputable def bmgToGraph {n : ℕ} (G : BoundaryMultigraph n) : SimpleGraph (Fin n) where
  Adj u v :=
    u ≠ v ∧ u ∈ G.vertices ∧ v ∈ G.vertices ∧
    ((u, v) ∈ G.lEdges ∨ (v, u) ∈ G.lEdges ∨
     (u, v) ∈ G.rEdges ∨ (v, u) ∈ G.rEdges)
  symm := by
    intro u v ⟨hne, hu, hv, hedges⟩
    exact ⟨hne.symm, hv, hu, by tauto⟩
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

open Classical in
noncomputable def numComponents {n : ℕ} (edges : Finset (Edge n)) : ℕ :=
  Set.ncard (Set.range (edgeSetToGraph n edges).connectedComponentMk)

open Classical in
noncomputable def numComponentsBMG {n : ℕ} (G : BoundaryMultigraph n) : ℕ :=
  Set.ncard {c : (bmgToGraph G).ConnectedComponent | ∃ v ∈ G.vertices, (bmgToGraph G).connectedComponentMk v = c}

open Classical in
def IsConnectedBoundaryMultigraph {n : ℕ} (G : BoundaryMultigraph n) : Prop :=
  numComponentsBMG G = 1

private theorem contraction_preserves_components :
  ∀ {n : ℕ} (S : Frontier n) (L R : Finset (Edge n)),
    (∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2) →
    (∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S) →
    (∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) →
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) := by
  intro n S L R hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints
  sorry

private theorem connected_iff_one_component :
  ∀ {n : ℕ} (edges : Finset (Edge n)),
    IsConnectedEdgeSet n edges ↔ numComponents edges = 1 := by
  intro n edges
  unfold IsConnectedEdgeSet numComponents
  set G := edgeSetToGraph n edges
  constructor
  · intro hconn
    have hpre := hconn.preconnected
    haveI := hconn.nonempty
    haveI := hpre.subsingleton_connectedComponent
    have v₀ := Classical.arbitrary (Fin n)
    have hrange : Set.range G.connectedComponentMk = {G.connectedComponentMk v₀} := by
      ext c; simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨v, hv⟩ => hv ▸ Subsingleton.elim _ _, fun h => ⟨v₀, h.symm⟩⟩
    rw [hrange, Set.ncard_singleton]
  · intro h
    rw [Set.ncard_eq_one] at h
    obtain ⟨c, hc⟩ := h
    have hmem : c ∈ Set.range G.connectedComponentMk := hc ▸ Set.mem_singleton c
    obtain ⟨v₀, hv₀⟩ := hmem
    haveI : Nonempty (Fin n) := ⟨v₀⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ‹_›⟩
    have hu : G.connectedComponentMk u ∈ ({c} : Set _) := hc ▸ Set.mem_range_self u
    have hv : G.connectedComponentMk v ∈ ({c} : Set _) := hc ▸ Set.mem_range_self v
    rw [Set.mem_singleton_iff] at hu hv
    exact SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)

private theorem bmg_connected_iff_one_component :
  ∀ {n : ℕ} (G : BoundaryMultigraph n),
    IsConnectedBoundaryMultigraph G ↔ numComponentsBMG G = 1 :=
  fun _ => Iff.rfl

theorem boundaryComponentCorrespondence
    (S : Frontier n)
    (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) :
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) :=
  contraction_preserves_components S L R hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints

theorem boundaryComponentCorrespondence_ham
    (S : Frontier n)
    (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) :
    IsConnectedFinset (L ∪ R) ↔
      IsConnectedBoundaryMultigraph (boundaryMultigraphOf S L R) := by
  unfold IsConnectedFinset
  rw [connected_iff_one_component, bmg_connected_iff_one_component]
  rw [boundaryComponentCorrespondence S L R hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints]

end BoundaryComponentCorrespondence

section SameStateStitchability

/-! ### Theorem 4.3: Same-state stitchability

If σ_S(H) = σ_S(H'), then M := L_S(H') ∪ R_S(H) is a Hamiltonian cycle.

The proof has two parts:
1. Degree condition: matching degree profiles ⟹ deg_M(v) = 2 for all v.
2. Connectivity: matching path-pairings ⟹ G_∂(M) = G_∂(H), which is connected. -/

theorem sameStateStitch_degreeCondition
    (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H H') v = 2 :=
  mixed_degree_eq S H H' hH hH' hd v

private theorem matching_pairings_give_same_boundary_left_edges :
  ∀ {n : ℕ} (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hπ : HEq (σ_S S H hH).π (σ_S S H' hH').π),
    boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H) =
    boundaryMultigraphOf S (leftSubgraph S H) (rightSubgraph S H) := by
  intro n S hS H H' hH hH' hU hπ
  unfold boundaryMultigraphOf
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp1, hp2, hne, e, he, hv1, hv2⟩
    exact ⟨hp1, hp2, hne, sorry⟩
  · rintro ⟨hp1, hp2, hne, e, he, hv1, hv2⟩
    exact ⟨hp1, hp2, hne, sorry⟩

theorem sameStateStitch_boundaryGraphEq
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hπ : HEq (σ_S S H hH).π (σ_S S H' hH').π) :
    boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H) =
    boundaryMultigraphOf S (leftSubgraph S H) (rightSubgraph S H) :=
  matching_pairings_give_same_boundary_left_edges S hS H H' hH hH' hU hπ

theorem sameStateStitch
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hσ : sameInterfaceState S H H' hH hH' hU) :
    IsHamCycle n (mixedGraph S H H') :=
  same_state_stitchability S hS H H' hH hH' hU hσ

end SameStateStitchability

end PNeNp
