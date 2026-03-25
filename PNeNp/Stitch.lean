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
    IsHamCycle n H → S.isBalanced →
    (rightSubgraph S H).Nonempty →
    ¬ hasPrematureCycle S H →
    ∀ comp : Finset (Edge n), comp ⊆ leftSubgraph S H → comp.Nonempty →
    (∀ v : Fin n, vertexDegreeIn n comp v ≤ 2) →
    ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) := by
  intro n S H hH _hS hRight hNoPrem comp hSub hNe _hDeg2 hCycle
  by_cases hcompH : comp = H
  · have hAll : H ⊆ S.leftEdges := fun e he =>
      (Finset.mem_inter.mp (hSub (hcompH ▸ he))).2
    have hempty : (rightSubgraph S H).Nonempty → False := by
      intro ⟨e, he⟩
      unfold rightSubgraph at he
      simp only [Finset.mem_inter] at he
      exact Finset.disjoint_left.mp S.disjoint (hAll he.1) he.2
    exact hempty hRight
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
    (hRight : (rightSubgraph S H).Nonempty)
    (hc : ¬ hasPrematureCycle S H) :
    PathComponentNormalFormResult S H where
  components_are_paths :=
    leftSubgraph_no_cycle_when_no_premature S H hH hS hRight hc
  endpoints_are_boundary :=
    degree_one_vertex_is_boundary S H hH hS hc
  pairing_determines_boundary := trivial

end PathComponentNormalForm

private theorem adj_mono {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hadj : (edgeSetToGraph n A).Adj u v) :
    (edgeSetToGraph n B).Adj u v :=
  ⟨hadj.1, h hadj.2⟩

private theorem reachable_mono {n : ℕ} {A B : Finset (Edge n)} (h : A ⊆ B)
    {u v : Fin n} (hreach : (edgeSetToGraph n A).Reachable u v) :
    (edgeSetToGraph n B).Reachable u v := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b _ hadj _ ih =>
    exact (SimpleGraph.Adj.reachable (adj_mono h hadj)).trans ih

open Classical in
private noncomputable def localEdgeComponentOf {n : ℕ} (edges : Finset (Edge n))
    (u : Fin n) : Finset (Edge n) :=
  edges.filter fun e =>
    ∃ v : Fin n, v ∈ e ∧ (edgeSetToGraph n edges).Reachable u v

open Classical in
private lemma localEdgeComponentOf_sub {n : ℕ} (edges : Finset (Edge n)) (u : Fin n) :
    localEdgeComponentOf edges u ⊆ edges :=
  Finset.filter_subset _ _

open Classical in
private lemma localEdgeComponentOf_nonempty {n : ℕ} (edges : Finset (Edge n))
    (u : Fin n) (hu : ∃ e ∈ edges, u ∈ e) :
    (localEdgeComponentOf edges u).Nonempty := by
  obtain ⟨e, he_mem, hu_in_e⟩ := hu
  exact ⟨e, Finset.mem_filter.mpr ⟨he_mem, u, hu_in_e, SimpleGraph.Reachable.refl u⟩⟩

open Classical in
private lemma localEdgeComponentOf_degree_eq {n : ℕ} (edges : Finset (Edge n))
    (u v : Fin n) (hreach : (edgeSetToGraph n edges).Reachable u v) :
    vertexDegreeIn n (localEdgeComponentOf edges u) v = vertexDegreeIn n edges v := by
  unfold vertexDegreeIn localEdgeComponentOf
  apply le_antisymm
  · exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  · apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_filter] at he ⊢
    obtain ⟨he_edges, hv_in_e⟩ := he
    exact ⟨⟨he_edges, v, hv_in_e, hreach⟩, hv_in_e⟩

open Classical in
private lemma localEdgeComponentOf_reachable {n : ℕ} (edges : Finset (Edge n))
    (u : Fin n) (v : Fin n)
    (hv : ∃ e ∈ localEdgeComponentOf edges u, v ∈ e) :
    (edgeSetToGraph n edges).Reachable u v := by
  obtain ⟨e, he, hv_in_e⟩ := hv
  simp only [localEdgeComponentOf, Finset.mem_filter] at he
  obtain ⟨he_edges, w, hw_in_e, hw_reach⟩ := he
  by_cases hwv : w = v
  · exact hwv ▸ hw_reach
  · exact hw_reach.trans (SimpleGraph.Adj.reachable ⟨hwv, by
      induction e using Sym2.ind with
      | h a b =>
        simp only [Sym2.mem_iff] at hw_in_e hv_in_e
        rcases hw_in_e with rfl | rfl <;> rcases hv_in_e with rfl | rfl
        · exact absurd rfl hwv
        · exact he_edges
        · rw [Sym2.eq_swap]; exact he_edges
        · exact absurd rfl hwv⟩)

open Classical in
private lemma localEdgeComponentOf_degree_le {n : ℕ} (edges : Finset (Edge n))
    (u v : Fin n) :
    vertexDegreeIn n (localEdgeComponentOf edges u) v ≤ vertexDegreeIn n edges v := by
  unfold vertexDegreeIn localEdgeComponentOf
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))

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

open Classical in
noncomputable def boundaryMultigraphOf (S : Frontier n)
    (L R : Finset (Edge n)) : BoundaryMultigraph n :=
  { vertices := boundaryVertices S
    lEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      vertexDegreeIn n L p.1 = 1 ∧ vertexDegreeIn n L p.2 = 1 ∧
      (edgeSetToGraph n L).Reachable p.1 p.2
    rEdges := Finset.univ.filter fun p =>
      p.1 ∈ boundaryVertices S ∧ p.2 ∈ boundaryVertices S ∧
      p.1 ≠ p.2 ∧
      vertexDegreeIn n R p.1 = 1 ∧ vertexDegreeIn n R p.2 = 1 ∧
      (edgeSetToGraph n R).Reachable p.1 p.2 }

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

open Classical in
private theorem every_component_has_boundary_vertex
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (c : (edgeSetToGraph n (L ∪ R)).ConnectedComponent)
    (hc : c ∈ Set.range (edgeSetToGraph n (L ∪ R)).connectedComponentMk) :
    ∃ v : Fin n, v ∈ boundaryVertices S ∧
      (edgeSetToGraph n (L ∪ R)).connectedComponentMk v = c := by
  obtain ⟨v₀, rfl⟩ := hc
  by_cases h1 : vertexDegreeIn n L v₀ = 1
  · exact ⟨v₀, hLEndpoints v₀ h1, rfl⟩
  · by_cases h2 : vertexDegreeIn n R v₀ = 1
    · exact ⟨v₀, hREndpoints v₀ h2, rfl⟩
    · have hv₀_deg : vertexDegreeIn n (L ∪ R) v₀ = 2 := hSpanning v₀
      have hv₀_pos : 0 < vertexDegreeIn n (L ∪ R) v₀ := by omega
      unfold vertexDegreeIn at hv₀_pos
      rw [Finset.card_pos] at hv₀_pos
      obtain ⟨e₀, he₀⟩ := hv₀_pos
      simp only [Finset.mem_filter] at he₀
      obtain ⟨he₀_mem, hv₀_in_e₀⟩ := he₀
      rcases Finset.mem_union.mp he₀_mem with he₀L | he₀R
      · have hv₀_L_pos : 0 < vertexDegreeIn n L v₀ := by
          unfold vertexDegreeIn; rw [Finset.card_pos]; exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀L, hv₀_in_e₀⟩⟩
        have hv₀_L_le : vertexDegreeIn n L v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
        have hv₀_L_ge2 : vertexDegreeIn n L v₀ ≥ 2 := by omega
        have hv₀_L_eq2 : vertexDegreeIn n L v₀ = 2 := by omega
        set comp := localEdgeComponentOf L v₀ with hcomp_def
        have hcomp_sub : comp ⊆ L := localEdgeComponentOf_sub L v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty L v₀ ⟨e₀, he₀L, hv₀_in_e₀⟩
        have hno_cycle := hLNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n L w :=
          localEdgeComponentOf_degree_le L v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc vertexDegreeIn n comp w
              ≤ vertexDegreeIn n L w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          rw [show 1 = 1 from rfl] at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_L : (edgeSetToGraph n L).Reachable v₀ w :=
          localEdgeComponentOf_reachable L v₀ w hw_incident
        have hw_L_deg : vertexDegreeIn n L w = 1 := by
          rw [← localEdgeComponentOf_degree_eq L v₀ w hw_reach_L]
          exact hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hLEndpoints w hw_L_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_left hw_reach_L
        exact ⟨w, hw_bdy, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩
      · have hv₀_R_pos : 0 < vertexDegreeIn n R v₀ := by
          unfold vertexDegreeIn; rw [Finset.card_pos]; exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀R, hv₀_in_e₀⟩⟩
        have hv₀_R_le : vertexDegreeIn n R v₀ ≤ vertexDegreeIn n (L ∪ R) v₀ := by
          unfold vertexDegreeIn
          exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
        have hv₀_R_ge2 : vertexDegreeIn n R v₀ ≥ 2 := by omega
        have hv₀_R_eq2 : vertexDegreeIn n R v₀ = 2 := by omega
        set comp := localEdgeComponentOf R v₀ with hcomp_def
        have hcomp_sub : comp ⊆ R := localEdgeComponentOf_sub R v₀
        have hcomp_ne : comp.Nonempty :=
          localEdgeComponentOf_nonempty R v₀ ⟨e₀, he₀R, hv₀_in_e₀⟩
        have hno_cycle := hRNoCycles comp hcomp_sub hcomp_ne
        push_neg at hno_cycle
        obtain ⟨w, hw⟩ := hno_cycle
        have hw_deg_le : vertexDegreeIn n comp w ≤ vertexDegreeIn n R w :=
          localEdgeComponentOf_degree_le R v₀ w
        have hw_le2 : vertexDegreeIn n comp w ≤ 2 := by
          calc vertexDegreeIn n comp w
              ≤ vertexDegreeIn n R w := hw_deg_le
            _ ≤ vertexDegreeIn n (L ∪ R) w := by
                unfold vertexDegreeIn
                exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
            _ = 2 := hSpanning w
        have hw_eq1 : vertexDegreeIn n comp w = 1 := by omega
        have hw_incident : ∃ e ∈ comp, w ∈ e := by
          unfold vertexDegreeIn at hw_eq1
          have hpos : 0 < (comp.filter fun e => w ∈ e).card := by omega
          obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
          simp only [Finset.mem_filter] at he
          exact ⟨e, he.1, he.2⟩
        have hw_reach_R : (edgeSetToGraph n R).Reachable v₀ w :=
          localEdgeComponentOf_reachable R v₀ w hw_incident
        have hw_R_deg : vertexDegreeIn n R w = 1 := by
          rw [← localEdgeComponentOf_degree_eq R v₀ w hw_reach_R]
          exact hw_eq1
        have hw_bdy : w ∈ boundaryVertices S := hREndpoints w hw_R_deg
        have hw_reach : (edgeSetToGraph n (L ∪ R)).Reachable v₀ w :=
          reachable_mono Finset.subset_union_right hw_reach_R
        exact ⟨w, hw_bdy, (SimpleGraph.ConnectedComponent.sound hw_reach).symm⟩

private lemma degree_add_of_disjoint {n : ℕ} (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R) (v : Fin n) :
    vertexDegreeIn n L v + vertexDegreeIn n R v = vertexDegreeIn n (L ∪ R) v := by
  unfold vertexDegreeIn; rw [Finset.filter_union]
  exact (Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hDisjoint)).symm

private lemma boundary_deg_one_one {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (v : Fin n) (hv : v ∈ boundaryVertices S) :
    vertexDegreeIn n L v = 1 ∧ vertexDegreeIn n R v = 1 := by
  have hadd := degree_add_of_disjoint L R hDisjoint v
  have htot := hSpanning v
  rcases hBdyDeg1 v hv with hL | hR <;> omega

private lemma non_bdy_full_L_deg {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (v : Fin n) (hv : v ∉ boundaryVertices S) (hpos : 0 < vertexDegreeIn n L v) :
    vertexDegreeIn n L v = 2 := by
  have hadd := degree_add_of_disjoint L R hDisjoint v
  have htot := hSpanning v
  have : vertexDegreeIn n L v ≠ 1 := fun h => hv (hLEndpoints v h)
  omega

open Classical in
private lemma bmg_adj_of_reachable_in_L
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n L u = 1) (hv_deg : vertexDegreeIn n L v = 1)
    (hreach : (edgeSetToGraph n L).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Adj u v := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · simp only [boundaryMultigraphOf, Finset.mem_filter]
    exact ⟨hu_bdy, Or.inl hu_deg⟩
  · simp only [boundaryMultigraphOf, Finset.mem_filter]
    exact ⟨hv_bdy, Or.inl hv_deg⟩
  · left
    simp only [boundaryMultigraphOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu_bdy, hv_bdy, hne, hu_deg, hv_deg, hreach⟩

open Classical in
private lemma bmg_adj_of_reachable_in_R
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n R u = 1) (hv_deg : vertexDegreeIn n R v = 1)
    (hreach : (edgeSetToGraph n R).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Adj u v := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · simp only [boundaryMultigraphOf, Finset.mem_filter]
    exact ⟨hu_bdy, Or.inr hu_deg⟩
  · simp only [boundaryMultigraphOf, Finset.mem_filter]
    exact ⟨hv_bdy, Or.inr hv_deg⟩
  · right; right; left
    simp only [boundaryMultigraphOf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu_bdy, hv_bdy, hne, hu_deg, hv_deg, hreach⟩

open Classical in
private lemma bmg_reachable_of_adj_boundary
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u b : Fin n) (hu : u ∈ boundaryVertices S) (hb : b ∈ boundaryVertices S)
    (hreach_L : (edgeSetToGraph n L).Reachable u b)
    (hu_deg : vertexDegreeIn n L u = 1) (hb_deg : vertexDegreeIn n L b = 1) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u b := by
  by_cases hne : u = b
  · subst hne; exact SimpleGraph.Reachable.refl u
  · exact (bmg_adj_of_reachable_in_L S L R u b hne hu hb hu_deg hb_deg hreach_L).reachable

open Classical in
private lemma walk_boundary_induction
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    ∀ (x v : Fin n) (hv : v ∈ boundaryVertices S)
      (w : (edgeSetToGraph n (L ∪ R)).Walk x v)
      (u : Fin n) (hu : u ∈ boundaryVertices S),
      ((edgeSetToGraph n L).Reachable u x ∧ vertexDegreeIn n L u = 1) ∨
      ((edgeSetToGraph n R).Reachable u x ∧ vertexDegreeIn n R u = 1) →
      (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v := by
  intro x v hv w
  induction w with
  | nil =>
    intro u hu hside
    rcases hside with ⟨hLreach, hLdeg⟩ | ⟨hRreach, hRdeg⟩
    · exact bmg_reachable_of_adj_boundary S L R hSpanning hLNoCycles hRNoCycles
        hLEndpoints hREndpoints hBdyDeg1 u v hu hv hLreach hLdeg
        (boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 v hv).1
    · have hv_R := (boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 v hv).2
      by_cases hne : u = v
      · subst hne; exact SimpleGraph.Reachable.refl u
      · exact (bmg_adj_of_reachable_in_R S L R u v hne hu hv hRdeg hv_R hRreach).reachable
  | @cons x y _ hadj_xy w' ih_w' =>
    intro u hu hside
    rcases hside with ⟨hLreach_ux, hLdeg_u⟩ | ⟨hRreach_ux, hRdeg_u⟩
    · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
      · have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
        exact ih_w' u hu (Or.inl ⟨hLreach_ux.trans hL_adj.reachable, hLdeg_u⟩)
      · by_cases hx_bdy : x ∈ boundaryVertices S
        · have ⟨hLx, hRx⟩ :=
            boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hx_bdy
          have hbmg_ux := bmg_reachable_of_adj_boundary S L R hSpanning hLNoCycles
            hRNoCycles hLEndpoints hREndpoints hBdyDeg1 u x hu hx_bdy hLreach_ux hLdeg_u hLx
          have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
          exact hbmg_ux.trans (ih_w' x hx_bdy (Or.inr ⟨hR_adj.reachable, hRx⟩))
        · exfalso
          have hR_pos : 0 < vertexDegreeIn n R x := by
            unfold vertexDegreeIn; rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_R, Sym2.mem_mk_left x y⟩⟩
          have hadd := degree_add_of_disjoint L R hDisjoint x
          have htot := hSpanning x
          by_cases hLx_pos : 0 < vertexDegreeIn n L x
          · have := non_bdy_full_L_deg S L R hDisjoint hSpanning hLEndpoints x hx_bdy hLx_pos
            omega
          · push_neg at hLx_pos; have hLx0 : vertexDegreeIn n L x = 0 := by omega
            have : u = x := by
              by_contra hne; obtain ⟨walk⟩ := hLreach_ux
              cases walk with
              | nil => exact hne rfl
              | cons hadj _ =>
                have : 0 < vertexDegreeIn n L x := by
                  unfold vertexDegreeIn; rw [Finset.card_pos]
                  exact ⟨_, Finset.mem_filter.mpr ⟨hadj.2, Sym2.mem_mk_left x _⟩⟩
                omega
            subst this; omega
    · rcases Finset.mem_union.mp hadj_xy.2 with hedge_L | hedge_R
      · by_cases hx_bdy : x ∈ boundaryVertices S
        · have ⟨hLx, hRx⟩ :=
            boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 x hx_bdy
          have hbmg_ux : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u x := by
            by_cases hne : u = x
            · subst hne; exact SimpleGraph.Reachable.refl u
            · exact (bmg_adj_of_reachable_in_R S L R u x hne hu hx_bdy
                hRdeg_u hRx hRreach_ux).reachable
          have hL_adj : (edgeSetToGraph n L).Adj x y := ⟨hadj_xy.1, hedge_L⟩
          exact hbmg_ux.trans (ih_w' x hx_bdy (Or.inl ⟨hL_adj.reachable, hLx⟩))
        · exfalso
          have hL_pos : 0 < vertexDegreeIn n L x := by
            unfold vertexDegreeIn; rw [Finset.card_pos]
            exact ⟨_, Finset.mem_filter.mpr ⟨hedge_L, Sym2.mem_mk_left x y⟩⟩
          have hadd := degree_add_of_disjoint L R hDisjoint x
          have htot := hSpanning x
          by_cases hRx_pos : 0 < vertexDegreeIn n R x
          · have hR1 : vertexDegreeIn n R x ≠ 1 := fun h => hx_bdy (hREndpoints x h)
            omega
          · push_neg at hRx_pos; have hRx0 : vertexDegreeIn n R x = 0 := by omega
            have : u = x := by
              by_contra hne; obtain ⟨walk⟩ := hRreach_ux
              cases walk with
              | nil => exact hne rfl
              | cons hadj _ =>
                have : 0 < vertexDegreeIn n R x := by
                  unfold vertexDegreeIn; rw [Finset.card_pos]
                  exact ⟨_, Finset.mem_filter.mpr ⟨hadj.2, Sym2.mem_mk_left x _⟩⟩
                omega
            subst this; omega
      · have hR_adj : (edgeSetToGraph n R).Adj x y := ⟨hadj_xy.1, hedge_R⟩
        exact ih_w' u hu (Or.inr ⟨hRreach_ux.trans hR_adj.reachable, hRdeg_u⟩)

private theorem reachable_in_union_gives_reachable_in_bmg
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v := by
  obtain ⟨w⟩ := hreach
  have ⟨hLu, _⟩ := boundary_deg_one_one S L R hDisjoint hSpanning hBdyDeg1 u hu
  exact walk_boundary_induction S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1 u v hv w u hu
    (Or.inl ⟨SimpleGraph.Reachable.refl u, hLu⟩)

private theorem reachable_in_bmg_gives_reachable_in_union
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hreach : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v) :
    (edgeSetToGraph n (L ∪ R)).Reachable u v := by
  suffices h : ∀ (a b : Fin n),
      (bmgToGraph (boundaryMultigraphOf S L R)).Reachable a b →
      (edgeSetToGraph n (L ∪ R)).Reachable a b from h u v hreach
  intro a b hrab
  obtain ⟨walk⟩ := hrab
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y _ hadj _ ih =>
    apply SimpleGraph.Reachable.trans _ ih
    simp only [bmgToGraph, boundaryMultigraphOf] at hadj
    obtain ⟨_, _, _, hedges⟩ := hadj
    have extract_reach : (edgeSetToGraph n (L ∪ R)).Reachable x y := by
      rcases hedges with hlr | hlr | hlr | hlr
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact reachable_mono Finset.subset_union_left hlr.2.2.2.2.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact (reachable_mono Finset.subset_union_left hlr.2.2.2.2.2).symm
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact reachable_mono Finset.subset_union_right hlr.2.2.2.2.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlr
        exact (reachable_mono Finset.subset_union_right hlr.2.2.2.2.2).symm
    exact extract_reach

open Classical in
private theorem component_map_well_defined
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1)
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hsame : (edgeSetToGraph n (L ∪ R)).connectedComponentMk u =
             (edgeSetToGraph n (L ∪ R)).connectedComponentMk v) :
    (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk u =
    (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk v := by
  have hreach : (edgeSetToGraph n (L ∪ R)).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hsame
  have hbmg := reachable_in_union_gives_reachable_in_bmg S L R hDisjoint
    hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints hBdyDeg1 u v hu hv hreach
  exact SimpleGraph.ConnectedComponent.sound hbmg

open Classical in
private theorem component_map_injective
    {n : ℕ} (S : Frontier n) (L R : Finset (Edge n))
    (u v : Fin n) (hu : u ∈ boundaryVertices S) (hv : v ∈ boundaryVertices S)
    (hsame : (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk u =
             (bmgToGraph (boundaryMultigraphOf S L R)).connectedComponentMk v) :
    (edgeSetToGraph n (L ∪ R)).connectedComponentMk u =
    (edgeSetToGraph n (L ∪ R)).connectedComponentMk v := by
  have hreach : (bmgToGraph (boundaryMultigraphOf S L R)).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact hsame
  have hunion := reachable_in_bmg_gives_reachable_in_union S L R u v hu hv hreach
  exact SimpleGraph.ConnectedComponent.sound hunion

open Classical in
private theorem contraction_preserves_components :
  ∀ {n : ℕ} (S : Frontier n) (L R : Finset (Edge n)),
    Disjoint L R →
    (∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2) →
    (∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)) →
    (∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S) →
    (∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S) →
    (∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) →
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) := by
  intro n S L R hDisjoint hSpanning hLNoCycles hRNoCycles hLEndpoints hREndpoints hBdyDeg1
  unfold numComponents numComponentsBMG
  set G := edgeSetToGraph n (L ∪ R)
  set B := boundaryMultigraphOf S L R
  set Gb := bmgToGraph B
  have hevery := every_component_has_boundary_vertex S L R hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints
  have hwd := component_map_well_defined S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1
  have hinj := component_map_injective S L R
  let repG : G.ConnectedComponent → Fin n := fun c =>
    (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose
  have hrepG_bdy : ∀ c, repG c ∈ boundaryVertices S :=
    fun c => (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose_spec.1
  have hrepG_eq : ∀ c, G.connectedComponentMk (repG c) = c :=
    fun c => (hevery c (c.ind (fun v => ⟨v, rfl⟩))).choose_spec.2
  let φ : G.ConnectedComponent → Gb.ConnectedComponent :=
    fun c => Gb.connectedComponentMk (repG c)
  suffices himg : φ '' (Set.range G.connectedComponentMk) =
      {c : Gb.ConnectedComponent | ∃ v ∈ B.vertices, Gb.connectedComponentMk v = c} by
    rw [← himg]
    exact (Set.ncard_image_of_injOn (fun c₁ _ c₂ _ heq => by
      rw [← hrepG_eq c₁, ← hrepG_eq c₂]
      exact hinj _ _ (hrepG_bdy c₁) (hrepG_bdy c₂) heq)).symm
  ext cb; constructor
  · rintro ⟨c, ⟨v₀, rfl⟩, rfl⟩
    exact ⟨repG (G.connectedComponentMk v₀), hrepG_bdy _, rfl⟩
  · rintro ⟨v, hv_mem, rfl⟩
    refine ⟨G.connectedComponentMk v, ⟨v, rfl⟩, ?_⟩
    exact hwd (repG (G.connectedComponentMk v)) v (hrepG_bdy _) hv_mem
      (hrepG_eq (G.connectedComponentMk v))

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
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    numComponents (L ∪ R) = numComponentsBMG (boundaryMultigraphOf S L R) :=
  contraction_preserves_components S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1

theorem boundaryComponentCorrespondence_ham
    (S : Frontier n)
    (L R : Finset (Edge n))
    (hDisjoint : Disjoint L R)
    (hSpanning : ∀ v : Fin n, vertexDegreeIn n (L ∪ R) v = 2)
    (hLNoCycles : ∀ comp : Finset (Edge n), comp ⊆ L → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hRNoCycles : ∀ comp : Finset (Edge n), comp ⊆ R → comp.Nonempty →
      ¬(∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2))
    (hLEndpoints : ∀ v : Fin n, vertexDegreeIn n L v = 1 → v ∈ boundaryVertices S)
    (hREndpoints : ∀ v : Fin n, vertexDegreeIn n R v = 1 → v ∈ boundaryVertices S)
    (hBdyDeg1 : ∀ v : Fin n, v ∈ boundaryVertices S →
      vertexDegreeIn n L v = 1 ∨ vertexDegreeIn n R v = 1) :
    IsConnectedFinset (L ∪ R) ↔
      IsConnectedBoundaryMultigraph (boundaryMultigraphOf S L R) := by
  unfold IsConnectedFinset
  rw [connected_iff_one_component, bmg_connected_iff_one_component]
  rw [boundaryComponentCorrespondence S L R hDisjoint hSpanning hLNoCycles hRNoCycles
    hLEndpoints hREndpoints hBdyDeg1]

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

private lemma danglingEndpoints_eq_degree_iff
    {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n))
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (v : Fin n) (hv : v ∈ boundaryVertices S) :
    vertexDegreeIn n (leftSubgraph S H) v = 1 ↔
    vertexDegreeIn n (leftSubgraph S H') v = 1 := by
  have fwd : v ∈ danglingEndpoints S H ↔ v ∈ danglingEndpoints S H' := by
    rw [hU]
  unfold danglingEndpoints at fwd
  simp only [Finset.mem_filter] at fwd
  unfold degreeProfile leftDegreeAt at fwd
  constructor
  · intro h; exact (fwd.mp ⟨hv, h⟩).2
  · intro h; exact (fwd.mpr ⟨hv, h⟩).2

private lemma same_pairing_implies_left_reachability_iff
    {n : ℕ} (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hπ : HEq (σ_S S H hH).π (σ_S S H' hH').π)
    (u v : Fin n)
    (hu_bdy : u ∈ boundaryVertices S) (hv_bdy : v ∈ boundaryVertices S)
    (hu_deg : vertexDegreeIn n (leftSubgraph S H) u = 1)
    (hv_deg : vertexDegreeIn n (leftSubgraph S H) v = 1) :
    (edgeSetToGraph n (leftSubgraph S H')).Reachable u v ↔
    (edgeSetToGraph n (leftSubgraph S H)).Reachable u v := by
  by_cases hne : u = v
  · subst hne; simp only [SimpleGraph.Reachable.refl, iff_self]
  · have hu_dang : u ∈ danglingEndpoints S H := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hu_bdy, hu_deg⟩
    have hv_dang : v ∈ danglingEndpoints S H := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hv_bdy, hv_deg⟩
    have hu_deg' : vertexDegreeIn n (leftSubgraph S H') u = 1 :=
      (danglingEndpoints_eq_degree_iff S H H' hU u hu_bdy).mp hu_deg
    have hv_deg' : vertexDegreeIn n (leftSubgraph S H') v = 1 :=
      (danglingEndpoints_eq_degree_iff S H H' hU v hv_bdy).mp hv_deg
    have hu_dang' : u ∈ danglingEndpoints S H' := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hu_bdy, hu_deg'⟩
    have hv_dang' : v ∈ danglingEndpoints S H' := by
      unfold danglingEndpoints
      simp only [Finset.mem_filter]
      exact ⟨hv_bdy, hv_deg'⟩
    have pairs_eq : (pathPairing S H hH).pairs = (pathPairing S H' hH').pairs := by
      have : ∀ (U U' : Finset (Fin n)) (M : PerfectMatching U) (M' : PerfectMatching U')
          (hUU : U = U') (hMM : HEq M M'), M.pairs = M'.pairs := by
        intro U _ M M' hUU hMM
        subst hUU
        exact congrArg PerfectMatching.pairs (eq_of_heq hMM)
      exact this _ _ _ _ hU hπ
    rw [← pathPairing_iff_reachable S H' hH' u v hu_dang' hv_dang' hne,
        ← pathPairing_iff_reachable S H hH u v hu_dang hv_dang hne,
        pairs_eq]

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
  · rintro ⟨hp1, hp2, hne, hdeg1, hdeg2, hreach⟩
    have hdeg1' := (danglingEndpoints_eq_degree_iff S H H' hU p.1 hp1).mpr hdeg1
    have hdeg2' := (danglingEndpoints_eq_degree_iff S H H' hU p.2 hp2).mpr hdeg2
    exact ⟨hp1, hp2, hne, hdeg1', hdeg2',
      (same_pairing_implies_left_reachability_iff S hS H H' hH hH' hU hπ
        p.1 p.2 hp1 hp2 hdeg1' hdeg2').mp hreach⟩
  · rintro ⟨hp1, hp2, hne, hdeg1, hdeg2, hreach⟩
    have hdeg1' := (danglingEndpoints_eq_degree_iff S H H' hU p.1 hp1).mp hdeg1
    have hdeg2' := (danglingEndpoints_eq_degree_iff S H H' hU p.2 hp2).mp hdeg2
    exact ⟨hp1, hp2, hne, hdeg1', hdeg2',
      (same_pairing_implies_left_reachability_iff S hS H H' hH hH' hU hπ
        p.1 p.2 hp1 hp2 hdeg1 hdeg2).mpr hreach⟩

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
