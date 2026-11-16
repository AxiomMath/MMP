module

public import MMP.AlgebraicGeometry.Singularities.Snc.RelativeSncOfSnc
public import MMP.AlgebraicGeometry.Vanishing.CoveringTrick

/-!
# The support of the pull-back of an effective Cartier divisor

Let `g : Y ⟶ X` be a dominant morphism from a locally Noetherian normal scheme to an integral
locally Noetherian normal scheme and `B` an effective Cartier divisor on `X`, with pull-back
`B' = g^*B`. Then `Supp B' = g⁻¹(Supp B)`.

If the generic point of a component `Q` of `B'` mapped outside `Supp B`, then `1` would be a local
equation of `B` near its image, whose pull-back `1` has order zero along `Q`. Conversely, if
`y ∉ Supp B'` but `g y ∈ Supp B`, a local equation `φ` of `B` near `g y` is regular at `g y`
(algebraic Hartogs, `B` being effective), and its pull-back, a local equation of `B'` near `y`, is
a unit at `y`. Since stalk maps are local, `φ` is then a unit at `g y`, so every prime divisor
through `g y` has coefficient `0` in `B`, a contradiction.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.coe_supp_eq_preimage_of_isPullback`: the statement
  above.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsIntegral X] in
/-- A rational function which is, at a point `x`, the image of a unit of `𝒪_{X,x}` has order zero
along every prime divisor through `x`. -/
theorem ord_eq_zero_of_isUnit_stalk {x : X} {W : irreducibleComponents X} (hx : x ∈ W.1)
    (φ : (RationalFunctions X)ˣ) (a : (X.presheaf.stalk x)ˣ)
    (ha : (stalkToRationalFunctions X hx).hom a = (φ : RationalFunctions X) W)
    (E : MMP.Mori.PrimeDivisor X) (hE : x ∈ E.support) : E.ord φ = 0 := by
  have hspec : E.genericPoint ⤳ x := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  obtain rfl : W = E.component := eq_of_mem_irreducibleComponents hx (E.support_subset_component hE)
  rw [PrimeDivisor.ord_eq_ordUnit]
  refine PrimeDivisor.ordUnit_eq_zero_of_isUnit E
    ((a.isUnit).map (X.presheaf.stalkSpecializes hspec).hom) ?_
  rw [E.toComponent_stalkSpecializes hspec hx, ha]
  rfl

/-- The support of the pull-back `B'` of a divisor `B` along a dominant morphism lies in the
inverse image of the support of `B`. -/
theorem coe_supp_subset_preimage_of_isPullback (g : Y ⟶ X) [IsDominant g] {B : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback g hB B') :
    (B'.supp : Set Y) ⊆ g ⁻¹' (B.supp : Set X) := by
  rw [coe_supp_eq_biUnion]
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨Q, hQ, hyQ⟩ := hy
  have hη : g Q.genericPoint ∈ (B.supp : Set X) := by
    by_contra hne
    let U : X.Opens := ⟨(B.supp : Set X)ᶜ, B.supp.isClosed.isOpen_compl⟩
    have hφ : B.IsLocalEquation U 1 := fun E ⟨x, hxE, hxU⟩ => by
      rw [PrimeDivisor.ord_eq_ordUnit, map_one, PrimeDivisor.ordUnit_one]
      by_contra hBE
      exact hxU (DivisorWithCoeffs.support_subset_supp hBE hxE)
    have hE : (Q.support ∩ g ⁻¹ᵁ U).Nonempty := by
      refine ⟨Q.genericPoint, ?_, hne⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have h1 := h U 1 hφ Q hE
    rw [pullbackComponent_eq hB hφ (Q.map_componentGenericPoint_mem g hE)
      (mem_pointComponent _) 1 (by simp), map_one, PrimeDivisor.ordUnit_one] at h1
    exact (Finsupp.mem_support_iff.mp hQ) h1
  have hcl : Q.support ⊆ g ⁻¹' (B.supp : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.2 hη)
      (B.supp.isClosed.preimage g.continuous)
  exact hcl hyQ

/-- The inverse image of the support of an effective Cartier divisor lies in the support of its
pull-back. -/
theorem preimage_subset_coe_supp_of_isPullback (g : Y ⟶ X) [IsDominant g] {B : Divisor X}
    (hBc : B.IsCartier) (hB0 : 0 ≤ B)
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback g hB B') :
    g ⁻¹' (B.supp : Set X) ⊆ (B'.supp : Set Y) := by
  intro y hy
  by_contra hyB'
  obtain ⟨U, hxU, φ, hφ⟩ := hBc (g y)
  obtain ⟨a, ha⟩ := (h.isLocalEquation hφ).exists_unit_stalk (show y ∈ g ⁻¹ᵁ U from hxU) hyB'
    (mem_pointComponent y)
  obtain ⟨s, hs⟩ := exists_stalk_eq_of_forall_zero_le_ord (mem_pointComponent (g y)) φ
    fun E hE => by rw [← hφ E ⟨g y, hE, hxU⟩]; exact hB0 E
  set Z := pointComponent y
  set z := componentGenericPoint Y Z
  have hzy : z ⤳ y := (isGenericPoint_componentGenericPoint Y Z).specializes
    (mem_pointComponent y)
  have hgzy : g z ⤳ g y := g.base.hom.map_specializes hzy
  have hzU : g z ∈ U := hgzy.mem_open U.isOpen hxU
  have hWz : g z ∈ (pointComponent (g y)).1 :=
    mem_irreducibleComponent_of_irreducibleSpace _ _
  obtain ⟨a₀, ha₀⟩ := hφ.exists_unit_stalk hzU (hB Z) hWz
  have hs₀ : (X.presheaf.stalkSpecializes hgzy).hom s = a₀ := by
    apply stalkToRationalFunctions_injective hWz
    rw [ha₀]
    change (X.presheaf.stalkSpecializes hgzy ≫ X.presheaf.stalkSpecializes _).hom s = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact hs
  have hsa : (g.stalkMap y).hom s = a := by
    apply stalkToRationalFunctions_injective (mem_pointComponent y)
    rw [ha]
    have e1 := congrArg Units.val ((pullbackLocalEquation_apply g hB hφ Z hzU).trans
      (pullbackComponent_eq hB hφ hzU hWz a₀ ha₀))
    change ((pullbackLocalEquation g hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z =
      (g.stalkMap z).hom a₀ at e1
    rw [e1, ← hs₀]
    change _ = (g.stalkMap z).hom ((X.presheaf.stalkSpecializes hgzy).hom s)
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]
    rfl
  have hsu : IsUnit s := (isUnit_map_iff (g.stalkMap y).hom s).mp (hsa ▸ a.isUnit)
  obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
  exact hE ((hφ E ⟨g y, hyE, hxU⟩).trans
    (ord_eq_zero_of_isUnit_stalk (mem_pointComponent (g y)) φ hsu.unit hs E hyE))

/-- **The support of the pull-back of an effective Cartier divisor is the inverse image of its
support.** For a dominant morphism `g : Y ⟶ X` from a locally Noetherian normal scheme to an
integral locally Noetherian normal scheme and an effective Cartier divisor `B` on `X` with
pull-back `B'`, `Supp B' = g⁻¹(Supp B)`. -/
theorem coe_supp_eq_preimage_of_isPullback (g : Y ⟶ X) [IsDominant g] {B : Divisor X}
    (hBc : B.IsCartier) (hB0 : 0 ≤ B)
    {hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback g hB B') :
    (B'.supp : Set Y) = g ⁻¹' (B.supp : Set X) :=
  (coe_supp_subset_preimage_of_isPullback g h).antisymm
    (preimage_subset_coe_supp_of_isPullback g hBc hB0 h)

end MMP.FourfoldProofs.FractionalLogComplexProof
