module

public import MMP.AlgebraicGeometry.Dimension.PureDimensional
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight

/-!
# Effective Cartier divisors on a variety are pure of codimension one

Let `X` be an integral scheme locally of finite type over a field (a variety) of dimension
`k + 1`, and `D` an effective Cartier divisor on `X`. Every irreducible component of `D` has
dimension `k` (Fulton, §1.7 and Appendix B.3.2).

The generic point `z` of a component has coheight `1` in `X` (Krull's principal ideal theorem,
`MMP.coheight_eq_one_of_isEffectiveCartierDivisor`), and on a variety
`height z + coheight z = dim X` (`MMP.height_add_coheight_eq_krullDim`), while the closure of `z`
has dimension `height z`.

## Main results

* `MMP.height_apply_of_isClosedImmersion`: a closed immersion preserves heights of points.
* `MMP.topologicalKrullDim_subscheme_eq_support`: a closed subscheme has the dimension of its
  support.
* `MMP.isPureDimensional_subscheme_of_isEffectiveCartierDivisor`: `D` is pure of dimension `k`.
* `MMP.hasDim_of_mem_irreducibleComponents_of_isEffectiveCartierDivisor`: its components have
  dimension `k`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §1.7 and Appendix B.3.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order Topology TopologicalSpace

universe u

namespace MMP

open MMP.Intersection (HasDim)

/-- The dimension of a scheme is the Krull dimension of its points under specialization. -/
private theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

variable {X Y : Scheme.{u}}

/-- A closed immersion is an order embedding of the specialization orders of points. -/
theorem le_iff_of_isClosedImmersion (ι : Y ⟶ X) [IsClosedImmersion ι] {a b : Y} :
    ι a ≤ ι b ↔ a ≤ b := by
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact ι.isClosedEmbedding.isInducing.specializes_iff

/-- A closed immersion is strictly monotone on points. -/
theorem strictMono_of_isClosedImmersion (ι : Y ⟶ X) [IsClosedImmersion ι] :
    StrictMono (fun a : Y ↦ ι a) := fun _ _ h ↦
  lt_of_le_not_ge ((le_iff_of_isClosedImmersion ι).2 h.le)
    fun h' ↦ h.not_ge ((le_iff_of_isClosedImmersion ι).1 h')

/-- A closed immersion preserves the height of points: every specialization of a point of the
image lies in the (closed) image. -/
theorem height_apply_of_isClosedImmersion (ι : Y ⟶ X) [IsClosedImmersion ι] (a : Y) :
    height (ι a) = height a := by
  refine (height_eq_of_strictMono _ (strictMono_of_isClosedImmersion ι) (fun a b hb ↦ ?_) a).symm
  have hb' : b ∈ closure {ι a} :=
    specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hb.le)
  obtain ⟨a', rfl⟩ : b ∈ Set.range ι :=
    (closure_minimal (by simp) ι.isClosedEmbedding.isClosed_range) hb'
  refine ⟨a', ?_, rfl⟩
  exact lt_of_le_not_ge ((le_iff_of_isClosedImmersion ι).1 hb.le)
    fun h' ↦ hb.not_ge ((le_iff_of_isClosedImmersion ι).2 h')

/-- A closed subscheme has the dimension of its support. -/
theorem topologicalKrullDim_subscheme_eq_support (I : X.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set X) := by
  have hemb := I.subschemeι.isClosedEmbedding.isEmbedding
  rw [← I.range_subschemeι]
  exact hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq

variable (K : Type u) [Field K] [X.Over (Spec (.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of K))]

include K in
/-- **Components of an effective Cartier divisor on a variety** (Fulton, §1.7). On an integral
scheme `X` locally of finite type over a field, of dimension `k + 1`, every irreducible component
of an effective Cartier divisor `D` has dimension `k`. -/
theorem hasDim_of_mem_irreducibleComponents_of_isEffectiveCartierDivisor {k : ℕ}
    (hX : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {Z : Set D.subscheme}
    (hZ : Z ∈ irreducibleComponents D.subscheme) : HasDim Z k := by
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  set z := D.subschemeι ζ with hz_def
  have hzD : z ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]
    exact ⟨ζ, rfl⟩
  have hmax : ∀ y ∈ D.support, y ⤳ z → y = z := by
    intro y hy hyz
    obtain ⟨y', rfl⟩ : y ∈ Set.range D.subschemeι := by
      rwa [D.range_subschemeι]
    rw [eq_of_specializes_of_mem_irreducibleComponents hZ hζ.def
      (D.subschemeι.isClosedEmbedding.isInducing.specializes_iff.1 hyz)]
  have hcoh : coheight z = 1 := coheight_eq_one_of_isEffectiveCartierDivisor K hD hzD hmax
  have hsum := height_add_coheight_eq_krullDim K z
  rw [hcoh, ← topologicalKrullDim_eq_krullDim] at hsum
  have key : height z + 1 = ((k + 1 : ℕ) : ℕ∞) := by
    have h := hsum.trans hX.symm
    exact_mod_cast h
  have hz : height z = k := by
    generalize height z = h at key ⊢
    induction h using ENat.recTopCoe with
    | top =>
      rw [top_add] at key
      exact absurd key (ENat.natCast_ne_top (k + 1)).symm
    | coe h =>
      have : h + 1 = k + 1 := by exact_mod_cast key
      exact_mod_cast Nat.add_right_cancel this
  refine ⟨k, rfl, ?_⟩
  have hcl := hζ.def
  subst hcl
  rw [topologicalKrullDim_closure_singleton_eq_height, ← height_apply_of_isClosedImmersion
    D.subschemeι, ← hz_def, hz]
  rfl

include K in
/-- **An effective Cartier divisor on a variety of dimension `k + 1` is pure of dimension `k`**
(Fulton, §1.7). -/
theorem isPureDimensional_subscheme_of_isEffectiveCartierDivisor {k : ℕ}
    (hX : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X) {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureDimensional D.subscheme k :=
  fun _ hZ ↦ hasDim_of_mem_irreducibleComponents_of_isEffectiveCartierDivisor K hX hD hZ

end MMP
