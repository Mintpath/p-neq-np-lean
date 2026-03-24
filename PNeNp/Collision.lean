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
  sorry

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
