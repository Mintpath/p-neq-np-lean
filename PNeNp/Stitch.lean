import PNeNp.Interface

namespace PNeNp

variable {n : ℕ}

/-!
Compatibility wrapper for the Section 4 stitchability API.
The canonical implementation now lives in `Interface.lean`.
-/

theorem sameStateStitch_degreeCondition
    (S : Frontier n)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hd : degreeProfile S H = degreeProfile S H')
    (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H H') v = 2 :=
  mixed_degree_eq S H H' hH hH' hd v

theorem sameStateStitch
    (S : Frontier n) (hS : S.isBalanced)
    (H H' : Finset (Edge n))
    (hH : IsHamCycle n H) (hH' : IsHamCycle n H')
    (hU : danglingEndpoints S H = danglingEndpoints S H')
    (hσ : sameInterfaceState S H H' hH hH' hU) :
    IsHamCycle n (mixedGraph S H H') :=
  same_state_stitchability S hS H H' hH hH' hU hσ

end PNeNp
