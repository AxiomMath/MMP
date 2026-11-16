module

public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf

/-!
# The relative divisorial stable base locus

For a morphism `f : X ⟶ Z` of normal varieties and a real divisor `D` on `X`, a prime divisor `G`
of `X` lies in the *relative divisorial stable base locus* of `D` if, over every open
neighbourhood `U` of the generic point of `f(G)`, every effective real divisor
`L = D|_{f⁻¹U} + ∑ aⱼ div(gⱼ)` contains `G` with positive coefficient. For an integral divisor
`D`, the *relative fixed multiplicity* along `G` is the least order of vanishing along `G` of a
nonzero section of `𝒪_X(D)` over some `f⁻¹U`.

## Main definitions

* `MMP.Fourfold.IsInRelativeDivisorialStableBase`.
* `MMP.Fourfold.relativeFixedMultiplicity`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {X Z : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Z)

/-- A real divisor `L` is *effective on* an open `V ⊆ X`: its restriction to `V` is effective,
that is, `L` has nonnegative coefficient along every prime divisor meeting `V`. -/
def IsEffectiveOn (L : RDivisor X) (V : X.Opens) : Prop :=
  ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → 0 ≤ L.coeff P

/-- A prime divisor `G` of `X` belongs to the *relative divisorial stable base locus* of a real
divisor `D` (for `f : X ⟶ Z`) if for every open neighbourhood `U` of the generic point `f(η_G)`
of `closure f(G)` and every real divisor `L = D + ∑ⱼ aⱼ div(gⱼ)` (`aⱼ ∈ ℝ`, `gⱼ ∈ k(X)^*`)
effective on `f⁻¹U`, the coefficient of `G ∩ f⁻¹U` in `L` is positive. If there is no such
effective representative the condition holds. -/
@[mmp "def_fourfold_divisorial_stable_base"]
def IsInRelativeDivisorialStableBase (D : RDivisor X) (G : MMP.Mori.PrimeDivisor X) : Prop :=
  ∀ U : Z.Opens, f G.genericPoint ∈ U →
    ∀ (s : ℕ) (a : Fin s → ℝ) (g : Fin s → (RationalFunctions X)ˣ),
      IsEffectiveOn (D + ∑ j, a j • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
          (principalDivisor (g j))) (f ⁻¹ᵁ U) →
        0 < (D + ∑ j, a j • Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
          (principalDivisor (g j))).coeff G

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A prime divisor whose generic point maps into `U` meets `f⁻¹U`. -/
theorem support_inter_preimage_nonempty {G : MMP.Mori.PrimeDivisor X} {U : Z.Opens}
    (h : f G.genericPoint ∈ U) : (G.support ∩ (f ⁻¹ᵁ U : Set X)).Nonempty :=
  (G.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp h

/-- The order of vanishing along `G` of a section `φ` of `𝒪_X(D)` over an open `V` meeting `G`:
the largest `n ≥ 0` with `v_G(φ) + d_G ≥ n`, that is, the coefficient of `G` in `div φ + D`
(`⊤` for `φ_G = 0`). -/
def sectionVanishingOrder (D : Divisor X) (G : MMP.Mori.PrimeDivisor X) {V : X.Opens}
    (h : (G.support ∩ (V : Set X)).Nonempty) (φ : D.divisorialSubmodule V) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : G.OrdGE ((n : ℤ) - D.coeff G)
    (φ.1 ⟨G.component, G.componentGenericPoint_mem_of_nonempty h⟩)), (n : ℕ∞)

/-- The *relative fixed multiplicity* of an integral divisor `D` at a prime divisor `G` (for
`f : X ⟶ Z`): the minimum, over the open neighbourhoods `U` of `f(η_G)` and the nonzero sections
`φ` of `𝒪_X(D)` over `f⁻¹U`, of the order of vanishing of `φ` along `G`; it is `⊤` when there are
no nonzero relative sections near the generic image of `G`. -/
@[mmp "def_fourfold_divisorial_stable_base"]
def relativeFixedMultiplicity (D : Divisor X) (G : MMP.Mori.PrimeDivisor X) : ℕ∞ :=
  ⨅ (U : Z.Opens) (hU : f G.genericPoint ∈ U) (φ : D.divisorialSubmodule (f ⁻¹ᵁ U))
    (_ : φ ≠ 0), sectionVanishingOrder D G (support_inter_preimage_nonempty f hU) φ

end MMP.Fourfold
