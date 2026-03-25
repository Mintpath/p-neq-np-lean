import PNeNp.Interface
import PNeNp.Stitch

namespace PNeNp

variable {n : ℕ}

/-! ## Section 5: Different-State Collision Is Fatal

This file formalizes the collision theorems from Section 5 of the
Hamiltonian route paper. The two error mechanisms are:
  - Degree-profile collision (Theorem 5.3): unconditional.
  - Pairing-mismatch collision (Corollary 5.6): requires overlay disconnectedness.

Irreducible combinatorial facts are axiomatized; proof structure matches the paper. -/

section FrontierTranscriptMap

/-! ### Definition 5.1: Frontier transcript map m_S

The frontier transcript m_S(H) is the vector of gate values at frontier S
when circuit C is evaluated on input H. Formally,
  m_S(H) := (g(H))_{g ∈ ∂_S(C)}
where ∂_S(C) is the set of gates whose output crosses frontier S.

Already defined in Interface.lean as `frontierTranscript`. -/

end FrontierTranscriptMap

section RectangleProperty

/-! ### Lemma 5.2: Rectangle property

If m_S(H) = m_S(H'), then the right subcircuit sees identical inputs
for H and H' (for any right input x_R), hence:
  C(x_L^{H'}, x_R) = C(x_L^{H}, x_R)  for all x_R.

In particular, C accepts the mixed input iff it accepts H:
  C(x_L^{H'}, x_R^{H}) = C(x_L^{H}, x_R^{H}) = 1.

Already stated in Interface.lean as `rectangle_property`. We state
the key corollary: the circuit accepts the mixed-graph encoding. -/

theorem rectangleProperty_mixedAccepted {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H)
    (hCorrect : C.eval (toInput H) = true)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H')) :
    C.eval (toInput (mixedGraph S H H')) = true := by
  have h := rectangle_property C S toInput H H' hm
  rw [h, hCorrect]

end RectangleProperty

section DegreeProfileCollision

/-! ### Theorem 5.3: Degree-profile collision forces circuit error

Let C be a correct circuit for Ham_n. If ∃ Hamiltonian cycles H, H' with
  m_S(H) = m_S(H')  but  d_S(H) ≠ d_S(H'),
then C is incorrect on at least one input.

Proof: The rectangle property gives C(mixed input) = C(H) = 1.
But d_S(H) ≠ d_S(H') means some boundary vertex v has d_S(H)(v) ≠ d_S(H')(v),
so deg_M(v) = d_S(H')(v) + (2 - d_S(H)(v)) ≠ 2.
Hence M is not 2-regular, not Hamiltonian, but the circuit accepts it. -/

private theorem mixed_degree_decomposition
    {n : ℕ} (S : Frontier n) (H H' : Finset (Edge n)) (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H H') v =
    leftDegreeAt S H' v + rightDegreeAt S H v := by
  unfold mixedGraph vertexDegreeIn leftDegreeAt rightDegreeAt vertexDegreeIn
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H'))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
  rw [Finset.card_union_of_disjoint hdisj]

theorem degreeCollision_mixedNot2Regular
    (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H ≠ degreeProfile S H') :
    ∃ v : Fin n, vertexDegreeIn n (mixedGraph S H H') v ≠ 2 := by
  rw [Ne, funext_iff] at hd
  push_neg at hd
  obtain ⟨v, hv⟩ := hd
  refine ⟨v, ?_⟩
  rw [mixed_degree_decomposition S H H' v]
  have hH_split := leftDeg_add_rightDeg_eq_two S H hH v
  have hH'_split := leftDeg_add_rightDeg_eq_two S H' hH' v
  unfold degreeProfile at hv
  omega

theorem degreeCollision_mixedNotHam
    (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H ≠ degreeProfile S H') :
    ¬ IsHamCycle n (mixedGraph S H H') := by
  intro hHam
  obtain ⟨v, hv⟩ := degreeCollision_mixedNot2Regular S H H' hH hH' hd
  exact hv (hHam.twoRegular v)

theorem degreeProfileCollisionForcesError {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H ≠ degreeProfile S H') :
    False :=
  degree_collision_forces_error C S toInput H H' hH hH' hCorrect hm hd

end DegreeProfileCollision

section PairingOverlayTheory

/-! ### Definition 5.4': Pairing overlay O(π,ρ)

For perfect matchings π, ρ on a set U of even cardinality,
the overlay graph O(π,ρ) is the 2-regular multigraph on U
with edges π ∪ ρ, which decomposes into disjoint even cycles.

Already defined in Interface.lean as `overlayGraph`. -/

end PairingOverlayTheory

section OneCycleOverlayCount

/-! ### Lemma 5.4: Exact count of one-cycle overlays

Fix a perfect matching ρ on U with |U| = 2t, t ≥ 2. The number of
perfect matchings π such that O(π,ρ) is a single 2t-cycle is exactly
  2^{t-1} · (t-1)!

Proof: Cyclic orderings of the t ρ-blocks give (t-1)! choices.
Binary endpoint choices at t-1 transitions give 2^{t-1} choices.
Product: 2^{t-1} · (t-1)!.

Already stated in Interface.lean as `one_cycle_overlay_count`. -/

end OneCycleOverlayCount

section PairingMismatchWitness

/-! ### Lemma 5.5: Pairing-mismatch witness

With |U_S(H)| = 2t ≥ 4, the number of perfect matchings π' producing
a disconnected overlay with ρ_S(H) is exactly
  (2t-1)!! - 2^{t-1}·(t-1)!

The connected fraction is Θ(t^{1/2} · 2^{-t}), so almost all pairings
produce disconnected overlays for large t. -/

theorem pairingMismatchWitness_exact (t : ℕ) (ht : t ≥ 2)
    {U : Finset (Fin n)} (hU : U.card = 2 * t)
    (ρ : PerfectMatching U) :
    numPerfectMatchings U - numSingleCycleOverlays ρ =
    Nat.doubleFactorial (2 * t - 1) - 2 ^ (t - 1) * (t - 1).factorial := by
  have h1 : 1 ≤ t := by omega
  rw [total_perfect_matchings_eq t h1 U hU, one_cycle_overlay_count t ht hU ρ]

theorem pairingMismatchWitness_count (t : ℕ) (ht : t ≥ 2)
    {U : Finset (Fin n)} (hU : U.card = 2 * t)
    (ρ : PerfectMatching U) :
    numPerfectMatchings U - numSingleCycleOverlays ρ > 0 := by
  rw [pairingMismatchWitness_exact t ht hU ρ]
  exact Nat.sub_pos_of_lt (disconnected_overlay_dominates t ht)

theorem pairingMismatchWitness_asymptotic (t : ℕ) (ht : t ≥ 2) :
    2 ^ (t - 1) * (t - 1).factorial < Nat.doubleFactorial (2 * t - 1) :=
  disconnected_overlay_dominates t ht

end PairingMismatchWitness

section PairingMismatchCollision

/-! ### Corollary 5.6: Pairing-mismatch collision forces circuit error

Let S be a balanced frontier, H a Hamiltonian cycle with |U_S(H)| = 2t ≥ 4.
Let H' be a Hamiltonian cycle with:
  - d_S(H') = d_S(H)           (degree profiles match)
  - c_S(H') = c_S(H) = 0       (no premature cycles)
  - O(π_S(H'), ρ_S(H)) disconnected

Then M = L_S(H') ∪ R_S(H) is 2-regular but not connected, hence not Hamiltonian.

If also m_S(H') = m_S(H), the circuit accepts the mixed input (rectangle property)
while M is not Hamiltonian. Circuit error. -/

theorem pairingMismatch_twoRegularButDisconnected
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisc : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    (∀ v : Fin n, vertexDegreeIn n (mixedGraph S H H') v = 2) ∧
    ¬ IsHamCycle n (mixedGraph S H H') :=
  ⟨fun v => mixed_degree_eq S H H' hH hH' hd v,
   pairing_mismatch_not_hamiltonian S hS H H' hH hH' hd hU hDisc⟩

theorem pairingMismatchCollisionForcesError {m : ℕ}
    (C : BooleanCircuit m) (S : Frontier n)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hS : S.isBalanced)
    (hCorrect : CircuitDecidesHAM C toInput)
    (hm : frontierTranscript C S (toInput H) = frontierTranscript C S (toInput H'))
    (hd : degreeProfile S H = degreeProfile S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hDisc : overlayIsDisconnected
      (hU ▸ pathPairing S H' hH')
      (danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH)) :
    False :=
  pairing_mismatch_collision_forces_error C S toInput H H' hH hH' hS hCorrect hm hd hU hDisc

/-! The boundary multigraph of M equals the overlay O(π_S(H'), ρ_S(H)).
Uses `numComponentsBMG` from Stitch.lean for the boundary multigraph
component count rather than a separate axiom. -/

private theorem bmg_vertices_eq_dangling
    {n : ℕ} (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H') :
    (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)).vertices =
    danglingEndpoints S H := by
  unfold boundaryMultigraphOf danglingEndpoints
  ext v; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbv, hdeg⟩
    constructor
    · exact hbv
    · rcases hdeg with h | h
      · have hv_dang' : v ∈ danglingEndpoints S H' := by
          unfold danglingEndpoints; simp only [Finset.mem_filter]
          exact ⟨hbv, by unfold degreeProfile leftDegreeAt; exact h⟩
        rw [← hU] at hv_dang'
        exact (Finset.mem_filter.mp hv_dang').2
      · unfold degreeProfile leftDegreeAt
        have h2 := leftDeg_add_rightDeg_eq_two S H hH v
        unfold leftDegreeAt rightDegreeAt at h2
        omega
  · rintro ⟨hbv, hdeg⟩
    constructor
    · exact hbv
    · left
      have hv_dang : v ∈ danglingEndpoints S H := by
        unfold danglingEndpoints; simp only [Finset.mem_filter]; exact ⟨hbv, hdeg⟩
      rw [hU] at hv_dang
      unfold danglingEndpoints at hv_dang
      have hfilt := (Finset.mem_filter.mp hv_dang).2
      unfold degreeProfile leftDegreeAt at hfilt
      exact hfilt

private theorem cast_pairs_eq
    {n : ℕ} {U V : Finset (Fin n)} (h : U = V) (M : PerfectMatching V) :
    (h ▸ M).pairs = M.pairs := by
  subst h; rfl

private theorem bmg_ledge_of_pair
    {n : ℕ} (S : Frontier n)
    (H' : Finset (Edge n)) (hH' : IsHamCycle n H')
    (R : Finset (Edge n))
    (p : Fin n × Fin n) (hp : p ∈ (pathPairing S H' hH').pairs) :
    (p.1, p.2) ∈ (boundaryMultigraphOf S (leftSubgraph S H') R).lEdges := by
  unfold boundaryMultigraphOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hp1 := (pathPairing S H' hH').fst_mem p hp
  have hp2 := (pathPairing S H' hH').snd_mem p hp
  exact ⟨dangling_mem_boundary S H' p.1 hp1,
         dangling_mem_boundary S H' p.2 hp2,
         (pathPairing S H' hH').ne_pair p hp,
         dangling_left_deg_one S H' p.1 hp1,
         dangling_left_deg_one S H' p.2 hp2,
         pathPairing_reflects_components S H' hH' p hp⟩

private theorem bmg_redge_of_pair
    {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (L : Finset (Edge n))
    (p : Fin n × Fin n) (hp : p ∈ (rightPairing S H hH).pairs) :
    (p.1, p.2) ∈ (boundaryMultigraphOf S L (rightSubgraph S H)).rEdges := by
  unfold boundaryMultigraphOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hp1 := (rightPairing S H hH).fst_mem p hp
  have hp2 := (rightPairing S H hH).snd_mem p hp
  have hp1_bdy : p.1 ∈ boundaryVertices S := by
    unfold rightDanglingEndpoints at hp1; exact (Finset.mem_filter.mp hp1).1
  have hp2_bdy : p.2 ∈ boundaryVertices S := by
    unfold rightDanglingEndpoints at hp2; exact (Finset.mem_filter.mp hp2).1
  have hp1_deg : vertexDegreeIn n (rightSubgraph S H) p.1 = 1 := by
    unfold rightDanglingEndpoints rightDegreeAt at hp1
    exact (Finset.mem_filter.mp hp1).2
  have hp2_deg : vertexDegreeIn n (rightSubgraph S H) p.2 = 1 := by
    unfold rightDanglingEndpoints rightDegreeAt at hp2
    exact (Finset.mem_filter.mp hp2).2
  exact ⟨hp1_bdy, hp2_bdy,
         (rightPairing S H hH).ne_pair p hp,
         hp1_deg, hp2_deg,
         rightPairing_reflects_components S H hH p hp⟩

private theorem pair_of_bmg_ledge
    {n : ℕ} (S : Frontier n)
    (H' : Finset (Edge n)) (hH' : IsHamCycle n H')
    (R : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hle : (u, v) ∈ (boundaryMultigraphOf S (leftSubgraph S H') R).lEdges) :
    (u, v) ∈ (pathPairing S H' hH').pairs ∨ (v, u) ∈ (pathPairing S H' hH').pairs := by
  unfold boundaryMultigraphOf at hle
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hle
  obtain ⟨hu_bdy, hv_bdy, _, hu_deg, hv_deg, hreach⟩ := hle
  have hu_dang : u ∈ danglingEndpoints S H' := by
    unfold danglingEndpoints; simp only [Finset.mem_filter]
    exact ⟨hu_bdy, by unfold degreeProfile leftDegreeAt; exact hu_deg⟩
  have hv_dang : v ∈ danglingEndpoints S H' := by
    unfold danglingEndpoints; simp only [Finset.mem_filter]
    exact ⟨hv_bdy, by unfold degreeProfile leftDegreeAt; exact hv_deg⟩
  exact (pathPairing_iff_reachable S H' hH' u v hu_dang hv_dang hne).mpr hreach

private theorem pair_of_bmg_redge
    {n : ℕ} (S : Frontier n)
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (L : Finset (Edge n))
    (u v : Fin n) (hne : u ≠ v)
    (hre : (u, v) ∈ (boundaryMultigraphOf S L (rightSubgraph S H)).rEdges) :
    (u, v) ∈ (rightPairing S H hH).pairs ∨ (v, u) ∈ (rightPairing S H hH).pairs := by
  unfold boundaryMultigraphOf at hre
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hre
  obtain ⟨hu_bdy, hv_bdy, _, hu_deg, hv_deg, hreach⟩ := hre
  have hu_rdang : u ∈ rightDanglingEndpoints S H := by
    unfold rightDanglingEndpoints; simp only [Finset.mem_filter]
    exact ⟨hu_bdy, by unfold rightDegreeAt; exact hu_deg⟩
  have hv_rdang : v ∈ rightDanglingEndpoints S H := by
    unfold rightDanglingEndpoints; simp only [Finset.mem_filter]
    exact ⟨hv_bdy, by unfold rightDegreeAt; exact hv_deg⟩
  exact (rightPairing_iff_reachable S H hH u v hu_rdang hv_rdang hne).mpr hreach

private theorem bmg_adj_iff_overlay_adj
    {n : ℕ} (S : Frontier n) (_hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (_hd : degreeProfile S H = degreeProfile S H')
    (_hc : ¬ hasPrematureCycle S H)
    (_hc' : ¬ hasPrematureCycle S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (u v : Fin n) :
    let π' := hU ▸ pathPairing S H' hH'
    let ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
    (bmgToGraph (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H))).Adj u v ↔
    (overlayGraph π' ρ).Adj u v := by
  set L := leftSubgraph S H'
  set R := rightSubgraph S H
  set BMG := boundaryMultigraphOf S L R
  set π' := hU ▸ pathPairing S H' hH'
  set ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
  have hπ'_pairs : π'.pairs = (pathPairing S H' hH').pairs :=
    cast_pairs_eq hU (pathPairing S H' hH')
  have hρ_pairs : ρ.pairs = (rightPairing S H hH).pairs :=
    cast_pairs_eq (danglingEndpoints_eq_rightDanglingEndpoints S H hH) (rightPairing S H hH)
  have hverts := bmg_vertices_eq_dangling S H H' hH hH' hU
  constructor
  · intro hadj
    have hne := hadj.1
    have hedges := hadj.2.2.2
    show (overlayGraph π' ρ).Adj u v
    unfold overlayGraph
    rcases hedges with hle | hle | hre | hre
    · have := pair_of_bmg_ledge S H' hH' R u v hne hle
      left; rw [hπ'_pairs]
      rcases this with hp | hp
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_ledge S H' hH' R v u (Ne.symm hne) hle
      left; rw [hπ'_pairs]
      rcases this with hp | hp
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_redge S H hH L u v hne hre
      right; rw [hρ_pairs]
      rcases this with hp | hp
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
    · have := pair_of_bmg_redge S H hH L v u (Ne.symm hne) hre
      right; rw [hρ_pairs]
      rcases this with hp | hp
      · exact ⟨(v, u), hp, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨(u, v), hp, Or.inl ⟨rfl, rfl⟩⟩
  · intro hovl
    show (bmgToGraph BMG).Adj u v
    unfold overlayGraph at hovl
    rcases hovl with ⟨p, hp, hpuv⟩ | ⟨p, hp, hpuv⟩
    · rw [hπ'_pairs] at hp
      have hne : u ≠ v := by
        rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (pathPairing S H' hH').ne_pair p hp
        · exact ((pathPairing S H' hH').ne_pair p hp).symm
      have hp1_dang' := (pathPairing S H' hH').fst_mem p hp
      have hp2_dang' := (pathPairing S H' hH').snd_mem p hp
      have hle := bmg_ledge_of_pair S H' hH' R p hp
      rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne,
          hverts ▸ (hU ▸ hp1_dang' : p.1 ∈ danglingEndpoints S H),
          hverts ▸ (hU ▸ hp2_dang' : p.2 ∈ danglingEndpoints S H),
          Or.inl hle⟩
      · exact ⟨hne,
          hverts ▸ (hU ▸ hp2_dang' : p.2 ∈ danglingEndpoints S H),
          hverts ▸ (hU ▸ hp1_dang' : p.1 ∈ danglingEndpoints S H),
          Or.inr (Or.inl hle)⟩
    · rw [hρ_pairs] at hp
      have hne : u ≠ v := by
        rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (rightPairing S H hH).ne_pair p hp
        · exact ((rightPairing S H hH).ne_pair p hp).symm
      have hp1_rdang := (rightPairing S H hH).fst_mem p hp
      have hp2_rdang := (rightPairing S H hH).snd_mem p hp
      have hDE := danglingEndpoints_eq_rightDanglingEndpoints S H hH
      have hre := bmg_redge_of_pair S H hH L p hp
      rcases hpuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne,
          hverts ▸ (hDE ▸ hp1_rdang : p.1 ∈ danglingEndpoints S H),
          hverts ▸ (hDE ▸ hp2_rdang : p.2 ∈ danglingEndpoints S H),
          Or.inr (Or.inr (Or.inl hre))⟩
      · exact ⟨hne,
          hverts ▸ (hDE ▸ hp2_rdang : p.2 ∈ danglingEndpoints S H),
          hverts ▸ (hDE ▸ hp1_rdang : p.1 ∈ danglingEndpoints S H),
          Or.inr (Or.inr (Or.inr hre))⟩

private theorem same_adj_same_components
    {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (hadj : ∀ u v : Fin n, G₁.Adj u v ↔ G₂.Adj u v) :
    Set.ncard {c : G₁.ConnectedComponent | ∃ v ∈ U, G₁.connectedComponentMk v = c} =
    Set.ncard {c : G₂.ConnectedComponent | ∃ v ∈ U, G₂.connectedComponentMk v = c} := by
  have hG : G₁ = G₂ := by
    ext u v; exact hadj u v
  subst hG; rfl

private theorem boundary_multigraph_equals_overlay_components :
  ∀ {n : ℕ} (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hc : ¬ hasPrematureCycle S H)
    (hc' : ¬ hasPrematureCycle S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H'),
    let π' := hU ▸ pathPairing S H' hH'
    let ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
    numComponentsBMG (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)) =
    overlayComponentCount π' ρ := by
  intro n S hS H H' hH hH' hd hc hc' hU
  set BMG := boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)
  set π' := hU ▸ pathPairing S H' hH'
  set ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
  unfold numComponentsBMG overlayComponentCount
  have hverts := bmg_vertices_eq_dangling S H H' hH hH' hU
  rw [hverts]
  exact same_adj_same_components (bmgToGraph BMG) (overlayGraph π' ρ)
    (danglingEndpoints S H)
    (bmg_adj_iff_overlay_adj S hS H H' hH hH' hd hc hc' hU)

theorem pairingMismatch_boundaryIsOverlay
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (hc : ¬ hasPrematureCycle S H)
    (hc' : ¬ hasPrematureCycle S H')
    (hU : danglingEndpoints S H = danglingEndpoints S H') :
    let π' := hU ▸ pathPairing S H' hH'
    let ρ := danglingEndpoints_eq_rightDanglingEndpoints S H hH ▸ rightPairing S H hH
    numComponentsBMG (boundaryMultigraphOf S (leftSubgraph S H') (rightSubgraph S H)) =
    overlayComponentCount π' ρ := by
  exact boundary_multigraph_equals_overlay_components S hS H H' hH hH' hd hc hc' hU

end PairingMismatchCollision

end PNeNp
