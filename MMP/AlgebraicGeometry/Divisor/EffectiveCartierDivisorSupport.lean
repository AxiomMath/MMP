module

public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisor
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullback

/-!
# The support of the subscheme of an effective Cartier divisor

For an effective Cartier divisor `D`, the support of its closed subscheme is the support `|D|`
(`MMP.CartierDivisor.coe_support_subscheme`), and the subscheme of a sum is the product of the
ideal sheaves (`MMP.CartierDivisor.subscheme_add`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.3 and Appendix B.4.4.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MMP.Intersection MMP.CartierDivisorSheaf MMP.CartierDivisorPullback

universe u

namespace MMP.CartierDivisor

variable {X : Scheme.{u}}

/-- The support `|D|` of an effective Cartier divisor `D` lies in the support of its closed
subscheme: at a point outside the latter, a local equation of `D` in `𝒪_X` is a unit nearby, so
`D` vanishes near that point. -/
theorem support_subset_support_subscheme {D : X.CartierDivisor} (hD : IsEffective D) :
    cartierSupport D ⊆ ((subscheme D hD).support : Set X) := by
  intro x hx
  by_contra hxI
  obtain ⟨U, hU, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
  obtain ⟨g, hg⟩ := hU
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hxU,
    ideal_subscheme_affine hD hg, Scheme.mem_zeroLocus_iff] at hxI
  push Not at hxI
  obtain ⟨f, hf, hxf⟩ := hxI
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [Scheme.basicOpen_mul] at hxf
  have hxg : x ∈ X.basicOpen g := hxf.2
  have hle : X.basicOpen g ≤ (U : X.Opens) := X.basicOpen_le g
  obtain ⟨hu, hloc⟩ := hg
  have hres : IsUnit ((X.presheaf.map (homOfLE hle).op).hom g) :=
    RingedSpace.isUnit_res_basicOpen X.toRingedSpace g
  have hV : restrictDivisor D (X.basicOpen g) = 0 := by
    have h1 := isLocalEquation_restrict hle hloc
    have heq : Units.map (resK hle).toMonoidHom hu.unit =
        Units.map (toTotalQuotient (X.basicOpen g)).toMonoidHom hres.unit := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
      exact resK_toK hle g
    rw [heq] at h1
    exact h1.symm.trans (cartierClass_map_units _ _)
  exact (notMem_cartierSupport_iff (U := U) hxU).mpr ⟨X.basicOpen g, hxg, hle, hV⟩ hx

/-- Off the support `|D|` of an effective Cartier divisor, the closed subscheme of `D` is empty:
a local equation `g ∈ 𝒪(U)` of `D` has a unit germ there. -/
theorem notMem_support_subscheme {D : X.CartierDivisor} (hD : IsEffective D) {x : X}
    (hx : x ∉ cartierSupport D) : x ∉ ((subscheme D hD).support : Set X) := by
  obtain ⟨U, hU, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
  obtain ⟨g, hu, hloc⟩ := hU
  obtain ⟨a, ha⟩ := exists_isGermUnit hloc hxU hx
  have haval : a.val = X.presheaf.germ U x hxU g := by
    apply stalkToTotalQuotient_injective X
    rw [ha, IsUnit.unit_spec, stalkToTotalQuotient_germ]
  have htop : AlgebraicGeometry.IdealSheafData.stalk (subscheme D hD) x = ⊤ := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ _ U hxU,
      ideal_subscheme_affine hD ⟨hu, hloc⟩, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_eq_top, ← haval]
    exact a.isUnit
  exact (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mp htop

/-- The support of the closed subscheme of an effective Cartier divisor `D` is `|D|`. -/
theorem coe_support_subscheme {D : X.CartierDivisor} (hD : IsEffective D) :
    ((subscheme D hD).support : Set X) = cartierSupport D :=
  Set.Subset.antisymm (fun _ hx ↦ not_not.mp fun h ↦ notMem_support_subscheme hD h hx)
    (support_subset_support_subscheme hD)

/-- The product of local equations in `𝒪_X` of `D` and `E` is a local equation of `D + E`. -/
theorem IsRegularLocalEquation.mul {D E : X.CartierDivisor} {U : X.Opens} {g h : Γ(X, U)}
    (hg : IsRegularLocalEquation D g) (hh : IsRegularLocalEquation E h) :
    IsRegularLocalEquation (D + E) (g * h) := by
  obtain ⟨hu, hgl⟩ := hg
  obtain ⟨hv, hhl⟩ := hh
  have huv : IsUnit (toK U (g * h)) := by rw [map_mul]; exact hu.mul hv
  refine ⟨huv, ?_⟩
  have : huv.unit = hu.unit * hv.unit := Units.ext (by simp)
  rw [this, IsLocalEquationOn, cartierClass_mul, hgl, hhl]
  simp only [restrictDivisor, map_add]

/-- The subscheme of a sum of effective Cartier divisors is the product of the ideal sheaves. -/
theorem subscheme_add {D E : X.CartierDivisor} (hD : IsEffective D) (hE : IsEffective E)
    (hDE : IsEffective (D + E)) :
    subscheme (D + E) hDE = subscheme D hD * subscheme E hE := by
  let ι := {U : X.affineOpens // IsEffectiveOn D U ∧ IsEffectiveOn E U}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := ι) (fun i ↦ i.1) ?_ fun i ↦ ?_
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨U, hU, hxU⟩ := exists_affineOpens_isEffectiveOn hD x
    obtain ⟨U', hU', hxU'⟩ := exists_affineOpens_isEffectiveOn hE x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (U : X.Opens) ⊓ U' from ⟨hxU, hxU'⟩) ((U : X.Opens) ⊓ U').isOpen
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨⟨V, hV⟩, hU.mono (hVU.trans inf_le_left), hU'.mono (hVU.trans inf_le_right)⟩, hxV⟩
  · obtain ⟨U, ⟨g, hg⟩, ⟨h, hh⟩⟩ := i
    change (subscheme (D + E) hDE).ideal U = (subscheme D hD * subscheme E hE).ideal U
    rw [ideal_subscheme_affine _ (hg.mul hh), Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      ideal_subscheme_affine hD hg, ideal_subscheme_affine hE hh,
      Ideal.span_singleton_mul_span_singleton]

end MMP.CartierDivisor
