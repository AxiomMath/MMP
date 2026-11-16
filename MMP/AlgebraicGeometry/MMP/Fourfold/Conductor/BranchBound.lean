module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SimultaneousModel
import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
import MMP.AlgebraicTopology.BorelMoore.CycleSpanRestriction
import MMP.AlgebraicGeometry.Resolution.ExceptionalGraphBalancedFlow
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalDefect
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.AdaptedOpen
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The branch bound by exceptional defects

Let `p : Y ⟶ X` be a projective birational morphism of normal projective complex fourfolds, with
`Y` `ℚ`-factorial and terminal, and let `Q = Q_1 ∪ ⋯ ∪ Q_m` be a reduced union of distinct prime
divisors of `Y` with `dim p(Q) ≤ 1`. Then the branch excess of `Q` is bounded by the divisor cycle
ranks of the normalizations of its components and the ranks of the punctured local systems along
the singular curves of `Y` lying in `Q`:
`∑_{V ⊆ Q} (r_V - 1) ≤ ∑_j ρ_*(Q_j^ν) + ∑_{T ⊆ Sing Y ∩ Q} b_T`,
where `V` runs over the irreducible surfaces of `Q` and `T` over the irreducible curves of
`Sing Y ∩ Q`. The proof injects the simultaneous kernel of the top surface maps of the
normalization non-isomorphism locus into the vertical defect over `Q` of a simultaneous
curve-and-point conductor model; no weight filtration enters.

## Main results

* `MMP.Fourfold.sum_boundaryBranchCount_sub_one_le_sum_curveLocalSystemRank`.

## Implementation notes

* The reduced union `Q` is a finite set of prime divisors of `Y`, as for
  `MMP.Fourfold.boundaryBranchCount`, which is `r_V`; `V ⊆ Q` means containment in the union of
  the supports. The left side is the finitely supported sum `∑ᶠ` in `ℤ` over irreducible closed
  subsets of dimension two contained in `Q`; its support is finite by
  `MMP.Fourfold.one_le_boundaryBranchCount_and_finite_setOf_one_lt`.
* `ρ_*(Q_j^ν)` is `MMP.Analytic.divisorCycleRank` of
  `MMP.Fourfold.primeDivisorNormalizationScheme`, over `ℂ` through `Q_j^ν ⟶ Y`, a complex scheme by
  `MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`.
* `b_T` is `MMP.Fourfold.curveLocalSystemRank`, computed on a local-system open `T° ⊆ T`
  (`MMP.Fourfold.IsLocalSystemOpen`). The theorem asserts that such opens exist, one for each
  irreducible curve `T ⊆ Sing Y`, and that the bound holds for them; since `b_T` does not depend
  on the open (`MMP.Fourfold.IsLocalSystemOpen.curveLocalSystemRank_eq`), it then holds for every
  choice.

## References

* [Termination for projective log canonical fourfolds with rational boundary (OpenAI, 2026)]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_thm_mmp_conductor_branch_bound_without_weights

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-- The Chow situation of schemes locally of finite type over `ℂ`. -/
local notation "𝔠" => Stacks.Chow.fieldChowSituation ℂ
/-- The delta-dimension of the points of a scheme over `ℂ`. -/
local notation "δ[" X "]" => Stacks.Chow.relativeDimension
  (Stacks.Chow.ChowSituation.dimensionFunction (Stacks.Chow.fieldChowSituation ℂ))
  (X ↘ Spec (CommRingCat.of ℂ))
/-- The rational `k`-cycles `Z_k(X)_ℚ` on a scheme over `ℂ`. -/
local notation "𝒵[" X ", " k "]" => MMP.Chow.RationalCycleGroup
  (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (CommRingCat.of ℂ)) k
/-- The proper push-forward `f_*` of rational `k`-cycles along a morphism over `ℂ`. -/
local notation "pf[" f ", " k "]" => MMP.Chow.rationalProperPushforward
  (Stacks.Chow.fieldChowSituation ℂ) _ _ k f
    (CategoryTheory.comp_over f (Spec (CommRingCat.of ℂ)))

/-- Linear algebra: if `Φ : ker α ⊓ ker β → D` is injective, then
`dim W ≤ dim (codomain of α) + dim (range β) + dim D`. -/
private lemma finrank_le_of_injective_ker {W A B D : Type*} [AddCommGroup W] [Module ℚ W]
    [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B] [AddCommGroup D] [Module ℚ D]
    [FiniteDimensional ℚ W] [FiniteDimensional ℚ A] [FiniteDimensional ℚ D]
    (α : W →ₗ[ℚ] A) (β : W →ₗ[ℚ] B)
    (Φ : ↥(LinearMap.ker α ⊓ LinearMap.ker β) →ₗ[ℚ] D) (hΦ : Function.Injective Φ) :
    Module.finrank ℚ W ≤ Module.finrank ℚ A + Module.finrank ℚ (LinearMap.range β) +
      Module.finrank ℚ D := by
  have h1 := LinearMap.finrank_range_add_finrank_ker α
  have h2 : Module.finrank ℚ (LinearMap.range α) ≤ Module.finrank ℚ A :=
    Submodule.finrank_le _
  have h3 := LinearMap.finrank_le_finrank_of_injective hΦ
  let γ := β.domRestrict (LinearMap.ker α)
  have h4 := LinearMap.finrank_range_add_finrank_ker γ
  have h5 : Module.finrank ℚ (LinearMap.range γ) ≤ Module.finrank ℚ (LinearMap.range β) :=
    Submodule.finrank_mono (LinearMap.range_domRestrict_le_range _ _)
  have h6 : Module.finrank ℚ (LinearMap.ker γ) ≤
      Module.finrank ℚ ↥(LinearMap.ker α ⊓ LinearMap.ker β) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.ker α).subtype.comp (LinearMap.ker γ).subtype |>.codRestrict _ ?_) ?_
    · intro x
      exact ⟨(x.1).2, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩
    · intro x y h
      have h' := congrArg (fun v : ↥(LinearMap.ker α ⊓ LinearMap.ker β) => (v : W)) h
      exact Subtype.ext (Subtype.ext h')
  omega

/-! ### Extending coefficient systems to a larger divisor -/

section Extend

variable {Z : Scheme.{0}} {B D : Divisor Z}

/-- A double surface of `B` is a double surface of any `D` whose support contains that of `B`. -/
private def ofSubset (hBD : B.support ⊆ D.support) (σ : DoubleSurface B) :
    DoubleSurface D where
  fst := σ.fst
  snd := σ.snd
  fst_mem := hBD σ.fst_mem
  snd_mem := hBD σ.snd_mem
  fst_ne_snd := σ.fst_ne_snd
  carrier := σ.carrier
  isComponent := σ.isComponent

/-- A double surface of `D` both of whose components lie in `B` is a double surface of `B`. -/
private def restrictOfMem (σ : DoubleSurface D) (h₁ : σ.fst ∈ B.support)
    (h₂ : σ.snd ∈ B.support) : DoubleSurface B where
  fst := σ.fst
  snd := σ.snd
  fst_mem := h₁
  snd_mem := h₂
  fst_ne_snd := σ.fst_ne_snd
  carrier := σ.carrier
  isComponent := σ.isComponent

open Classical in
/-- Extension by zero of a coefficient system of `B` to the double surfaces of `D ⊇ B`. -/
private noncomputable def extendCoeff (hBD : B.support ⊆ D.support) :
    (DoubleSurface B → ℚ) →ₗ[ℚ] (DoubleSurface D → ℚ) where
  toFun a σ := if h : σ.fst ∈ B.support ∧ σ.snd ∈ B.support then a (restrictOfMem σ h.1 h.2) else 0
  map_add' a b := by
    funext σ
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    funext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

private lemma extendCoeff_apply_ofSubset (hBD : B.support ⊆ D.support)
    (a : DoubleSurface B → ℚ) (σ : DoubleSurface B) :
    extendCoeff hBD a (ofSubset hBD σ) = a σ := by
  classical
  change (if h : σ.fst ∈ B.support ∧ σ.snd ∈ B.support then
    a (restrictOfMem (ofSubset hBD σ) h.1 h.2) else 0) = a σ
  rw [dif_pos ⟨σ.fst_mem, σ.snd_mem⟩]
  rfl

private lemma exists_eq_ofSubset_of_extendCoeff_ne_zero (hBD : B.support ⊆ D.support)
    {a : DoubleSurface B → ℚ} {σ : DoubleSurface D} (h : extendCoeff hBD a σ ≠ 0) :
    ∃ τ : DoubleSurface B, (ofSubset hBD τ) = σ ∧ a τ ≠ 0 := by
  classical
  change (if h : σ.fst ∈ B.support ∧ σ.snd ∈ B.support then
    a (restrictOfMem σ h.1 h.2) else 0) ≠ 0 at h
  split_ifs at h with h'
  · exact ⟨restrictOfMem σ h'.1 h'.2, rfl, h⟩
  · exact absurd rfl h

private lemma extendCoeff_mem_orientedSurfaceCoefficients (hBD : B.support ⊆ D.support)
    {a : DoubleSurface B → ℚ} (ha : a ∈ orientedSurfaceCoefficients B) :
    extendCoeff hBD a ∈ orientedSurfaceCoefficients D := by
  classical
  intro σ
  change (if h : σ.swap.fst ∈ B.support ∧ σ.swap.snd ∈ B.support then
    a (restrictOfMem σ.swap h.1 h.2) else 0) =
    -(if h : σ.fst ∈ B.support ∧ σ.snd ∈ B.support then a (restrictOfMem σ h.1 h.2) else 0)
  by_cases h : σ.fst ∈ B.support ∧ σ.snd ∈ B.support
  · rw [dif_pos ⟨h.2, h.1⟩, dif_pos h]
    exact ha (restrictOfMem σ h.1 h.2)
  · rw [dif_neg (fun h' => h ⟨h'.2, h'.1⟩), dif_neg h, neg_zero]

/-- On a component of `B`, the divisor of the extension is the divisor of the system. -/
private lemma surfaceCoefficientDivisor_extendCoeff_of_mem [NoetherianSpace Z]
    (hBD : B.support ⊆ D.support) (a : DoubleSurface B → ℚ) {G : MMP.Mori.PrimeDivisor Z}
    (hG : G ∈ B.support) :
    surfaceCoefficientDivisor (extendCoeff hBD a) G = surfaceCoefficientDivisor a G := by
  classical
  haveI : Finite (DoubleSurface B) := DoubleSurface.finite
  haveI : Finite (DoubleSurface D) := DoubleSurface.finite
  refine Finsupp.ext fun P => ?_
  change (surfaceCoefficientDivisor _ G).coeff P = (surfaceCoefficientDivisor a G).coeff P
  rw [coeff_surfaceCoefficientDivisor, coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff,
    surfaceCoefficientCoeff]
  letI : Fintype {σ : DoubleSurface B // σ.fst = G ∧
      σ.carrier = closure {G.idealSheaf.subschemeι P.genericPoint}} := Fintype.ofFinite _
  letI : Fintype {σ : DoubleSurface D // σ.fst = G ∧
      σ.carrier = closure {G.idealSheaf.subschemeι P.genericPoint}} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective (fun τ => ⟨(ofSubset hBD τ.1), τ.2⟩) ?_ _ _ ?_ ?_
  · intro τ τ' hττ
    have h' := congrArg Subtype.val hττ
    have h1 : τ.1.fst = τ'.1.fst := congrArg (fun σ : DoubleSurface D => σ.fst) h'
    have h2 : τ.1.snd = τ'.1.snd := congrArg (fun σ : DoubleSurface D => σ.snd) h'
    have h3 : τ.1.carrier = τ'.1.carrier := congrArg (fun σ : DoubleSurface D => σ.carrier) h'
    exact Subtype.ext (DoubleSurface.ext h1 h2 h3)
  · rintro ⟨σ, hσ⟩ hσr
    by_contra hne
    obtain ⟨τ, hτ, -⟩ := exists_eq_ofSubset_of_extendCoeff_ne_zero hBD hne
    have hτ' : ofSubset hBD τ = σ := hτ
    have hσ' := hσ
    rw [← hτ'] at hσ'
    exact hσr ⟨⟨τ, hσ'⟩, Subtype.ext hτ'⟩
  · intro τ
    exact (extendCoeff_apply_ofSubset hBD a τ.1).symm

/-- Off the components of `B`, the divisor of the extension vanishes. -/
private lemma surfaceCoefficientDivisor_extendCoeff_of_notMem [NoetherianSpace Z]
    (hBD : B.support ⊆ D.support) (a : DoubleSurface B → ℚ) {G : MMP.Mori.PrimeDivisor Z}
    (hG : G ∉ B.support) :
    surfaceCoefficientDivisor (extendCoeff hBD a) G = 0 := by
  classical
  refine Finsupp.ext fun P => ?_
  change (surfaceCoefficientDivisor _ G).coeff P = 0
  rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff]
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  by_contra hne
  obtain ⟨τ, hτ, -⟩ := exists_eq_ofSubset_of_extendCoeff_ne_zero hBD hne
  have h1 : τ.fst = σ.1.fst := congrArg (fun σ : DoubleSurface D => σ.fst) hτ
  exact hG (σ.2.1 ▸ h1 ▸ τ.fst_mem)

end Extend

/-! ### Divisors of coefficient systems -/

section Systems

open MMP MMP.Fourfold.ConductorBlowup
open scoped MMP.SubschemeOver

variable {Z : Scheme.{0}} {B : Divisor Z}

/-- The divisor `Zᵢ(a)` only depends on the values of `a` on the double surfaces with first
component `Eᵢ`. -/
private lemma surfaceCoefficientDivisor_congr {a a' : DoubleSurface B → ℚ}
    {E : MMP.Mori.PrimeDivisor Z} (h : ∀ σ : DoubleSurface B, σ.fst = E → a σ = a' σ) :
    surfaceCoefficientDivisor a E = surfaceCoefficientDivisor a' E := by
  have hc : surfaceCoefficientCoeff a E = surfaceCoefficientCoeff a' E := by
    funext P
    exact finsum_congr fun σ => h σ.1 σ.2.1
  unfold surfaceCoefficientDivisor
  rw [hc]

private lemma edgeSystem_apply_self (σ : DoubleSurface B) (t : ℚ) : edgeSystem σ t σ = t := by
  classical
  simp [edgeSystem]

private lemma edgeSystem_apply_of_ne (σ τ : DoubleSurface B) (t : ℚ) (h₁ : τ ≠ σ)
    (h₂ : τ ≠ σ.swap) : edgeSystem σ t τ = 0 := by
  classical
  simp [edgeSystem, h₁, h₂]

private lemma edgeSystem_mem_orientedSurfaceCoefficients (σ : DoubleSurface B) (t : ℚ) :
    edgeSystem σ t ∈ orientedSurfaceCoefficients B := by
  classical
  intro τ
  unfold edgeSystem
  by_cases h1 : τ = σ
  · subst h1
    rw [if_neg (swap_ne τ), if_pos rfl, if_pos rfl]
  · by_cases h2 : τ = σ.swap
    · subst h2
      rw [DoubleSurface.swap_swap, if_pos rfl, if_neg (swap_ne σ), if_pos rfl, neg_neg]
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h2 (by rw [← h, DoubleSurface.swap_swap])),
        if_neg (fun h => h1 (by rw [← DoubleSurface.swap_swap τ, h, DoubleSurface.swap_swap])),
        neg_zero]

/-- **Oriented cancellation.** For an oriented system `a` on a divisor `B` of a complex scheme
whose components are threefolds (every surface of a component has coheight one in it), the
classes `[Zᵢ(a)]` push forward to classes summing to zero in `H_4(Z, ℚ)`. -/
private lemma sum_componentHomologyMap_divisorClass_eq_zero' [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z]
    (hcoh : ∀ G ∈ B.support, ∀ x : G.idealSheaf.subscheme,
      topologicalKrullDim (closure ({x} : Set G.idealSheaf.subscheme)) =
        ((2 : ℕ) : WithBot ℕ∞) → Order.coheight x = 1)
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B) :
    ∑ E : B.support, componentHomologyMap E.1 4
      (Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1)) = 0 := by
  have hcx : ∀ E : MMP.Mori.PrimeDivisor Z, IsComplexScheme E.idealSheaf.subscheme :=
    fun E => IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  have key : ∑ E : B.support, pf[E.1.idealSheaf.subschemeι, (2 : ℕ)]
      (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1)) = 0 := by
    refine rationalCycleGroup_ext fun w => ?_
    rw [map_sum, map_zero]
    by_cases hw : δ[Z] w = 2
    · have h1 : ∀ E : B.support, Chow.rationalCoeff 𝔠 _ (2 : ℕ) w
          (pf[E.1.idealSheaf.subschemeι, (2 : ℕ)]
            (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1))) =
          ∑ᶠ σ : {σ : DoubleSurface B // σ.fst = E.1 ∧ σ.carrier = closure {w}}, a σ :=
        fun E => rationalCoeff_rationalProperPushforward_divisorCycle a E.1 (hcoh E.1 E.2) hw
      rw [Finset.sum_congr rfl fun E _ => h1 E]
      exact sum_finsum_doubleSurface_eq_zero B a ha _
    · exact Finset.sum_eq_zero fun E _ => rationalCoeff_eq_zero_of_relativeDimension_ne _ hw
  calc ∑ E : B.support, componentHomologyMap E.1 4
        (Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1))
      = ∑ E : B.support, Chow.rationalCycleClass Z 2 (pf[E.1.idealSheaf.subschemeι, (2 : ℕ)]
          (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1))) := by
        refine Finset.sum_congr rfl fun E _ => ?_
        haveI := hcx E.1
        rw [Chow.rationalCycleClass_rationalProperPushforward]
        rfl
    _ = 0 := by rw [← map_sum, key, map_zero]

/-- The Krull dimension of a subspace is monotone in the subset. -/
private lemma topologicalKrullDim_mono' {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) : topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val
    Topology.IsInducing.subtypeVal).topologicalKrullDim_le

/-- The coefficient systems supported on the double surfaces satisfying `P`. -/
private def supportedOn (B : Divisor Z) (P : DoubleSurface B → Prop) :
    Submodule ℚ (DoubleSurface B → ℚ) where
  carrier := {a | ∀ σ, a σ ≠ 0 → P σ}
  add_mem' {a b} ha hb σ h := by
    by_cases h' : a σ = 0
    · exact hb σ fun hb' => h (by simp [h', hb'])
    · exact ha σ h'
  zero_mem' σ h := absurd rfl h
  smul_mem' c a ha σ h := ha σ fun h' => h (by simp [h'])

/-- A point at which the surface cycle of a `ℚ`-divisor has a nonzero coefficient is the generic
point of one of its prime divisors. -/
private lemma exists_of_rationalCoeff_divisorCycle_ne_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (L : QDivisor X) {x : X}
    (hx : Chow.rationalCoeff 𝔠 _ (2 : ℕ) x (Chow.divisorCycle X L) ≠ 0) :
    ∃ P : MMP.Mori.PrimeDivisor X, L P ≠ 0 ∧ P.genericPoint = x := by
  by_cases h : ∃ P : MMP.Mori.PrimeDivisor X, P.genericPoint = x
  · obtain ⟨P, rfl⟩ := h
    refine ⟨P, fun hP => hx ?_, rfl⟩
    by_cases hd : δ[X] P.genericPoint = 2
    · rw [rationalCoeff_divisorCycle L P hd, hP]
    · exact rationalCoeff_eq_zero_of_relativeDimension_ne _ hd
  · push Not at h
    exact absurd (rationalCoeff_divisorCycle_eq_zero L h) hx

/-- Points with the same closure are equal. -/
private lemma eq_of_closure_eq {X : Scheme.{0}} {v w : X}
    (h : closure ({v} : Set X) = closure {w}) : v = w :=
  (inseparable_iff_closure_eq.2 h).eq

/-- A sum over the generic points of a set, which is at most one point, commutes with
scaling. -/
private lemma finsum_isGenericPoint_mul {X : Scheme.{0}} (T : Set X) (P : X → Prop)
    (d : X → ℚ) (k : ℚ) :
    ∑ᶠ (z : X) (_ : IsGenericPoint z T) (_ : P z), d z * k =
      (∑ᶠ (z : X) (_ : IsGenericPoint z T) (_ : P z), d z) * k := by
  classical
  by_cases h : ∃ z, IsGenericPoint z T ∧ P z
  · obtain ⟨z, hz, hP⟩ := h
    have key : ∀ g : X → ℚ, ∑ᶠ (y : X) (_ : IsGenericPoint y T) (_ : P y), g y = g z := by
      intro g
      rw [finsum_eq_single _ z]
      · simp only [finsum_eq_if, if_pos hz, if_pos hP]
      · intro y hy
        have : ¬ IsGenericPoint y T := fun hy' => hy (hy'.eq hz)
        simp only [finsum_eq_if, if_neg this]
    rw [key, key]
  · push Not at h
    have key : ∀ g : X → ℚ, ∑ᶠ (y : X) (_ : IsGenericPoint y T) (_ : P y), g y = 0 := by
      intro g
      refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
      by_cases hy : IsGenericPoint y T
      · simp only [finsum_eq_if, if_pos hy, if_neg (h y hy)]
      · simp only [finsum_eq_if, if_neg hy]
    rw [key, key, zero_mul]

open Classical in
/-- The balancing sum along `V` of a coefficient system, as a linear form. -/
private lemma balance_eq_sum {Y : Scheme.{0}} [Fintype (DoubleSurface B)] (r : Z ⟶ Y)
    (v : Y) (a : DoubleSurface B → ℚ) :
    (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = closure ({v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ) =
      ∑ σ, (if σ.fst.genericPoint ∉ exceptionalSet r ∧
          r.base '' σ.snd.support = closure ({v} : Set Y) then
        ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) else 0) * a σ := by
  classical
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [finsum_isGenericPoint_mul]
  split_ifs with hc
  · rw [finsum_eq_if, if_pos hc.1, finsum_eq_if, if_pos hc.2]
  · rw [zero_mul]
    by_cases h1 : σ.fst.genericPoint ∉ exceptionalSet r
    · rw [finsum_eq_if, if_pos h1, finsum_eq_if, if_neg fun h2 => hc ⟨h1, h2⟩]
    · rw [finsum_eq_if, if_neg h1]

/-- A double surface whose image has dimension at most one has no generic point over a
surface. -/
private lemma finsum_isGenericPoint_eq_zero_of_dim_le_one {Y : Scheme.{0}} (r : Z ⟶ Y)
    (hrc : IsClosedMap r.base) (σ : DoubleSurface B)
    (hσ : topologicalKrullDim (r.base '' σ.carrier) ≤ 1) (v : Y)
    (hv : topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞)) :
    ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
      (residueFieldDegree r z : ℚ) = 0 := by
  classical
  refine finsum_eq_zero_of_forall_eq_zero fun z => ?_
  by_cases hz : IsGenericPoint z σ.carrier
  · rw [finsum_eq_if, if_pos hz]
    by_cases hzV : r.base z = v
    · exfalso
      have hsub : closure ({v} : Set Y) ⊆ r.base '' σ.carrier := by
        rw [← hzV]
        exact closure_minimal (Set.singleton_subset_iff.2 ⟨z, hz.mem, rfl⟩)
          (hrc _ (isClosed_carrier σ))
      have := (topologicalKrullDim_mono' hsub).trans hσ
      rw [hv] at this
      exact absurd this (by decide)
    · rw [finsum_eq_if, if_neg hzV]
  · rw [finsum_eq_if, if_neg hz]

open Classical in
/-- The balancing form along `V`: `a ↦ ∑_σ [κ(z_σ) : κ(η_V)] a_σ`, over the double surfaces
with non-exceptional first component and second component over `V`. -/
private noncomputable def balanceₗ {Y : Scheme.{0}} [Fintype (DoubleSurface B)] (r : Z ⟶ Y)
    (v : Y) : (DoubleSurface B → ℚ) →ₗ[ℚ] ℚ :=
  ∑ σ, (if σ.fst.genericPoint ∉ exceptionalSet r ∧
      r.base '' σ.snd.support = closure ({v} : Set Y) then
    ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
      (residueFieldDegree r z : ℚ) else 0) • LinearMap.proj σ

private lemma finsum_balance_eq {Y : Scheme.{0}} [Fintype (DoubleSurface B)] (r : Z ⟶ Y)
    (v : Y) (a : DoubleSurface B → ℚ) :
    (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = closure ({v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ) = balanceₗ r v a := by
  classical
  rw [balance_eq_sum]
  simp only [balanceₗ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

open Classical in
private lemma balanceₗ_edgeSystem {Y : Scheme.{0}} [Fintype (DoubleSurface B)] (r : Z ⟶ Y)
    (v : Y) (τ : DoubleSurface B)
    (hτ : τ.snd.genericPoint ∈ exceptionalSet r) (t : ℚ) :
    balanceₗ r v (edgeSystem τ t) = t * (if τ.fst.genericPoint ∉ exceptionalSet r ∧
      r.base '' τ.snd.support = closure ({v} : Set Y) then
        ∑ᶠ (z : Z) (_ : IsGenericPoint z τ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) else 0) := by
  classical
  simp only [balanceₗ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Fintype.sum_eq_add τ τ.swap (swap_ne τ).symm]
  · rw [edgeSystem_apply_self]
    have h2 : edgeSystem τ t τ.swap = -t := by
      simp [edgeSystem, swap_ne τ]
    rw [h2, DoubleSurface.swap_fst]
    simp only [show ¬ (τ.snd.genericPoint ∉ exceptionalSet r) from not_not.2 hτ, false_and,
      if_false, mul_zero, add_zero]
    ring
  · intro σ hσ
    rw [edgeSystem_apply_of_ne _ _ _ hσ.1 hσ.2, mul_zero]

private lemma balanceₗ_eq_zero {Y : Scheme.{0}} [Fintype (DoubleSurface B)] (r : Z ⟶ Y)
    (hrc : IsClosedMap r.base) (v : Y)
    (hv : topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞))
    (a : DoubleSurface B → ℚ)
    (ha : ∀ σ, a σ ≠ 0 → topologicalKrullDim (r.base '' σ.carrier) ≤ 1) :
    balanceₗ r v a = 0 := by
  classical
  simp only [balanceₗ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h0 : a σ = 0
  · rw [h0, mul_zero]
  · rw [finsum_isGenericPoint_eq_zero_of_dim_le_one r hrc σ (ha σ h0) v hv]
    split_ifs <;> simp

end Systems

/-! ### The injection of the branch kernel into the vertical defect -/

section Injection

open MMP MMP.Fourfold.ConductorBlowup
open scoped MMP.SubschemeOver

variable {Y Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]

/-- The map `u ↦ ([∑_b u_{i,b} P_{i,b}])_i` from branch coefficients to the homology of the
normalized components. -/
private noncomputable def branchClassMap {ι : Type} (N : ι → Scheme.{0})
    [∀ i, (N i).Over (Spec (.of ℂ))] [∀ i, IsComplexScheme (N i)]
    (Br : ι → Type) [∀ i, Fintype (Br i)] (Pv : ∀ i, Br i → MMP.Mori.PrimeDivisor (N i)) :
    (∀ i, Br i → ℚ) →ₗ[ℚ] (∀ i, RationalHomology (N i) 4) :=
  LinearMap.pi fun i => Chow.divisorClass (N i) ∘ₗ
    ((∑ b : Br i, (Finsupp.lsingle (Pv i b)) ∘ₗ LinearMap.proj b) ∘ₗ LinearMap.proj i)

/-- **The branch kernel injects into the vertical defect.** Abstract form of the injection
`U → D_{v,Q}(r)`: the data are the strict components `st i` of the boundary `B` with their maps
`h i` to the normalized components `N i`, the branch legs `leg i b` over the conductor surfaces
`𝒱`, and the three inputs (strict-transform corrections `hκ`, generic balancing `hvert`,
contracted-edge injectivity through `D`). -/
private lemma card_le_of_branchLegs {X : Scheme.{0}} [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsNormal X] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    (sX : X ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (p : Y ⟶ X)
    (hrc : IsClosedMap r.base)
    (hf : MMP.Intersection.IsResolution sX (r ≫ p)) (hcompX : (r ≫ p) ≫ sX = Z ↘ Spec (.of ℂ))
    (hZ : IsProjective (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
    (B F D : Divisor Z) (hDsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) D)
    (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (hA : ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (r ≫ p) h)
    (hFB : F.support ⊆ B.support) (hBD : B.support ⊆ D.support)
    (hFex : ∀ E ∈ F.support, E.genericPoint ∈ exceptionalSet r)
    [FiniteDimensional ℚ (ComponentHomology F)]
    (hcoh : ∀ G ∈ B.support, ∀ x : G.idealSheaf.subscheme,
      topologicalKrullDim (closure ({x} : Set G.idealSheaf.subscheme)) =
        ((2 : ℕ) : WithBot ℕ∞) → Order.coheight x = 1)
    (Qs : Set Y) (hpQ : topologicalKrullDim (p.base '' Qs) ≤ 1)
    (hpdim : ∀ T : Set Y, IsClosed T → topologicalKrullDim T ≤ 1 →
      topologicalKrullDim (p.base '' T) ≤ 1)
    (hV2 : ∀ v w : Y, topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞) →
      topologicalKrullDim (closure ({w} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞) →
      closure ({w} : Set Y) ⊆ closure {v} → w = v)
    {ι : Type} [Fintype ι] (st : ι → MMP.Mori.PrimeDivisor Z) (hst_inj : Function.Injective st)
    (hst_B : ∀ i, st i ∈ B.support) (hst_F : ∀ i, st i ∉ F.support)
    (hst_ex : ∀ i, (st i).genericPoint ∉ exceptionalSet r)
    (hst_cov : ∀ G ∈ B.support, G ∉ F.support → ∃ i, st i = G)
    (hst_Q : ∀ i, r.base '' (st i).support ⊆ Qs)
    (𝒱 : Finset Y)
    (h𝒱 : ∀ v ∈ 𝒱, topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞))
    (hst_V : ∀ i, ∀ v ∈ 𝒱, r.base '' (st i).support ≠ closure ({v} : Set Y))
    (hVQ : ∀ v ∈ 𝒱, closure ({v} : Set Y) ⊆ Qs)
    (N : ι → Scheme.{0}) [∀ i, (N i).Over (Spec (.of ℂ))] [∀ i, IsComplexScheme (N i)]
    [∀ i, IsNormal (N i)] (hN : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (N i ↘ Spec (.of ℂ)))
    (h : ∀ i, (st i).idealSheaf.subscheme ⟶ N i) [∀ i, (h i).IsOver (Spec (.of ℂ))]
    (hM : ∀ i, MMP.Mori.IsProjectiveVariety ℂ ((st i).idealSheaf.subscheme ↘ Spec (.of ℂ)))
    (hMs : ∀ i, MMP.Mori.IsSmoothScheme ((st i).idealSheaf.subscheme ↘ Spec (.of ℂ)))
    (hMdim : ∀ i, topologicalKrullDim (st i).idealSheaf.subscheme = 3)
    (hhproj : ∀ i, IsProjectiveMorphism (h i))
    (hhbir : ∀ i, MMP.Mori.IsBirationalMorphism (h i))
    (Br : ι → Type) [∀ i, Fintype (Br i)] (Pv : ∀ i, Br i → MMP.Mori.PrimeDivisor (N i))
    (Vb : ∀ i, Br i → 𝒱) (leg : ∀ i, Br i → DoubleSurface B)
    (hleg_fst : ∀ i b, (leg i b).fst = st i) (hleg_snd : ∀ i b, (leg i b).snd ∈ F.support)
    (hleg_inj : ∀ i, Function.Injective (leg i))
    (hleg_img : ∀ i b, r.base '' (leg i b).carrier = closure ({(Vb i b).1} : Set Y))
    (hleg_sndimg : ∀ i b, r.base '' (leg i b).snd.support = closure ({(Vb i b).1} : Set Y))
    (hleg_div : ∀ i (u : Br i → ℚ),
      surfaceCoefficientDivisor (∑ b, edgeSystem (leg i b) (u b)) (st i) =
        inverseTransformDivisor (h i) (∑ b, Finsupp.single (Pv i b) (u b)))
    (hκ : ∀ i (c : QDivisor (st i).idealSheaf.subscheme),
      (∀ P ∈ c.support, topologicalKrullDim ((h i).base '' P.support) ≤ 1) →
      ∃ a ∈ orientedSurfaceCoefficients B,
        (∀ σ, a σ ≠ 0 → ((σ.fst = st i ∧ σ.snd ∈ F.support) ∨
            (σ.snd = st i ∧ σ.fst ∈ F.support)) ∧
          topologicalKrullDim (r.base '' σ.carrier) ≤ 1) ∧
        surfaceCoefficientDivisor a (st i) = c)
    (hvert : ∀ v ∈ 𝒱, ∀ a ∈ orientedSurfaceCoefficients B,
      (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = closure ({v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ = 0) →
      ∃ c ∈ orientedSurfaceCoefficients B,
        (∀ σ : DoubleSurface B, c σ ≠ a σ →
          r.base '' σ.fst.support = closure ({v} : Set Y) ∧
            r.base '' σ.snd.support = closure ({v} : Set Y)) ∧
        (∀ E ∈ B.support, r.base '' E.support = closure ({v} : Set Y) →
          Chow.rationalCoeff 𝔠 _ (2 : ℕ) v (componentPushforward r E 2
            (Chow.divisorCycle _ (surfaceCoefficientDivisor c E))) = 0) ∧
        ∀ σ : DoubleSurface B, c σ ≠ a σ → r.base '' σ.carrier ⊆ closure ({v} : Set Y)) :
    ∑ i, Fintype.card (Br i) ≤ 𝒱.card +
      Module.finrank ℚ (LinearMap.range (branchClassMap N Br Pv)) +
      Module.finrank ℚ (verticalDefectOver r F Qs) := by
  classical
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  haveI : Finite (DoubleSurface B) := DoubleSurface.finite
  letI : Fintype (DoubleSurface B) := Fintype.ofFinite _
  -- the weights, the balancing forms `α` and the classes `β`
  set w : ∀ i, Br i → ℚ := fun i b => ∑ᶠ (z : Z) (_ : IsGenericPoint z (leg i b).carrier)
    (_ : r.base z = (Vb i b).1), (residueFieldDegree r z : ℚ) with hw
  let α : (∀ i, Br i → ℚ) →ₗ[ℚ] (𝒱 → ℚ) := LinearMap.pi fun V =>
    ∑ i, ∑ b, (if Vb i b = V then w i b else 0) •
      ((LinearMap.proj b : (Br i → ℚ) →ₗ[ℚ] ℚ) ∘ₗ LinearMap.proj i)
  have hα : ∀ u V, α u V = ∑ i, ∑ b, (if Vb i b = V then w i b else 0) * u i b := by
    intro u V
    simp only [α, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  let β := branchClassMap N Br Pv
  have hβ : ∀ u i, β u i = Chow.divisorClass (N i) (∑ b, Finsupp.single (Pv i b) (u i b)) := by
    intro u i
    simp [β, branchClassMap]
  let U := LinearMap.ker α ⊓ LinearMap.ker β
  suffices hΦ : ∃ Φ : ↥U →ₗ[ℚ] ↥(verticalDefectOver r F Qs), Function.Injective Φ by
    obtain ⟨Φ, hΦ⟩ := hΦ
    have := finrank_le_of_injective_ker α β Φ hΦ
    rw [Module.finrank_pi_fintype] at this
    simpa using this
  -- the admissible systems
  let Zl : ∀ E : MMP.Mori.PrimeDivisor Z,
      (DoubleSurface B → ℚ) →ₗ[ℚ] QDivisor E.idealSheaf.subscheme :=
    fun E => surfaceCoefficientDivisorLinearMap B E
  let Sadm : Submodule ℚ (DoubleSurface B → ℚ) :=
    orientedSurfaceCoefficients B ⊓
    (⨅ i, LinearMap.ker (Chow.divisorClass _ ∘ₗ Zl (st i))) ⊓
    supportedOn B (fun σ => r.base '' σ.carrier ⊆ Qs) ⊓
    (⨅ E : F.support, LinearMap.ker
      (componentPushforward r E.1 2 ∘ₗ Chow.divisorCycle _ ∘ₗ Zl E.1))
  obtain ⟨A, hAS, hAleg⟩ : ∃ A : ↥U →ₗ[ℚ] (DoubleSurface B → ℚ), (∀ u, A u ∈ Sadm) ∧
      ∀ u i b, A u (leg i b) = (u : ∀ i, Br i → ℚ) i b := by
    let bU := Module.finBasis ℚ U
    have hβk : ∀ k i, Chow.divisorClass (N i)
        (∑ b, Finsupp.single (Pv i b) ((bU k : ∀ i, Br i → ℚ) i b)) = 0 := by
      intro k i
      have h0 := (Submodule.mem_inf.1 (bU k).2).2
      rw [LinearMap.mem_ker] at h0
      rw [← hβ]
      exact congrFun h0 i
    have hαk : ∀ k (V : 𝒱), ∑ i, ∑ b, (if Vb i b = V then w i b else 0) *
        (bU k : ∀ i, Br i → ℚ) i b = 0 := by
      intro k V
      have h0 := (Submodule.mem_inf.1 (bU k).2).1
      rw [LinearMap.mem_ker] at h0
      rw [← hα]
      exact congrFun h0 V
    -- strict-transform corrections on the strict components
    choose c hc0 hc using fun k i => exists_divisorClass_inverseTransformDivisor_add_eq_zero
      (hM i) (hMs i) (hMdim i) (hN i) (h i) (hhproj i) (hhbir i) _ (hβk k i)
    choose a1 ha1o ha1s ha1d using fun k i => hκ i (c k i) (hc0 k i)
    -- the branch legs and the system before balancing
    let e : Fin (Module.finrank ℚ U) → DoubleSurface B → ℚ := fun k =>
      ∑ i, ∑ b, edgeSystem (leg i b) ((bU k : ∀ i, Br i → ℚ) i b)
    let a0 : Fin (Module.finrank ℚ U) → DoubleSurface B → ℚ := fun k => e k + ∑ i, a1 k i
    have heo : ∀ k, e k ∈ orientedSurfaceCoefficients B := fun k =>
      Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun b _ =>
        edgeSystem_mem_orientedSurfaceCoefficients _ _
    have ha0o : ∀ k, a0 k ∈ orientedSurfaceCoefficients B := fun k =>
      Submodule.add_mem _ (heo k) (Submodule.sum_mem _ fun i _ => ha1o k i)
    have he_ne : ∀ k σ, e k σ ≠ 0 → ∃ i b, σ = leg i b ∨ σ = (leg i b).swap := by
      intro k σ hσ
      simp only [e, Finset.sum_apply] at hσ
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
      obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
      refine ⟨i, b, ?_⟩
      by_contra hne
      push Not at hne
      exact hb (edgeSystem_apply_of_ne _ _ _ hne.1 hne.2)
    have hleg_ne_swap : ∀ i b j b', leg i b ≠ (leg j b').swap := by
      intro i b j b' h
      apply hst_F i
      rw [← hleg_fst i b, h, DoubleSurface.swap_fst]
      exact hleg_snd j b'
    have he_leg : ∀ k i b, e k (leg i b) = (bU k : ∀ i, Br i → ℚ) i b := by
      intro k i b
      simp only [e, Finset.sum_apply]
      rw [Finset.sum_eq_single i, Finset.sum_eq_single b, edgeSystem_apply_self]
      · intro b' _ hb'
        exact edgeSystem_apply_of_ne _ _ _ (fun h => hb' (hleg_inj i h).symm)
          (hleg_ne_swap i b i b')
      · simp
      · intro j _ hj
        refine Finset.sum_eq_zero fun b' _ => edgeSystem_apply_of_ne _ _ _ ?_
          (hleg_ne_swap i b j b')
        intro h
        apply hj
        apply hst_inj
        rw [← hleg_fst j b', ← h, hleg_fst]
      · simp
    have hdim_leg : ∀ i b, ¬ topologicalKrullDim (r.base '' (leg i b).carrier) ≤ 1 := by
      intro i b h0
      rw [hleg_img, h𝒱 _ (Vb i b).2] at h0
      exact absurd h0 (by decide)
    have ha1_leg : ∀ k i j b, a1 k j (leg i b) = 0 := by
      intro k i j b
      by_contra h0
      exact hdim_leg i b ((ha1s k j) _ h0).2
    -- the balancing condition holds before balancing
    have hbal : ∀ k (V : 𝒱),
        (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
          (_ : r.base '' σ.snd.support = closure ({V.1} : Set Y)) (z : Z)
          (_ : IsGenericPoint z σ.carrier) (_ : r.base z = V.1),
            (residueFieldDegree r z : ℚ) * a0 k σ) = 0 := by
      intro k V
      rw [finsum_balance_eq]
      simp only [a0, e, map_add, map_sum]
      rw [Finset.sum_eq_zero fun i _ =>
          balanceₗ_eq_zero r hrc V.1 (h𝒱 _ V.2) _ fun σ h0 => (ha1s k i σ h0).2,
        add_zero]
      rw [← hαk k V]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
      rw [balanceₗ_edgeSystem r V.1 _ (hFex _ (hleg_snd i b)), mul_comm]
      congr 1
      by_cases hV : Vb i b = V
      · subst hV
        rw [if_pos ⟨hleg_fst i b ▸ hst_ex i, hleg_sndimg i b⟩, if_pos rfl]
      · rw [if_neg, if_neg hV]
        rintro ⟨-, h2⟩
        exact hV (Subtype.ext (eq_of_closure_eq ((hleg_sndimg i b).symm.trans h2)))
    choose cv hcvo hcv1 hcv2 hcv3 using fun k (V : 𝒱) =>
      hvert V.1 V.2 (a0 k) (ha0o k) (hbal k V)
    let Ak : Fin (Module.finrank ℚ U) → DoubleSurface B → ℚ := fun k =>
      a0 k + ∑ V : 𝒱, (cv k V - a0 k)
    have hδ : ∀ k (V : 𝒱) σ, (cv k V - a0 k) σ ≠ 0 →
        r.base '' σ.fst.support = closure ({V.1} : Set Y) ∧
          r.base '' σ.carrier ⊆ closure ({V.1} : Set Y) := by
      intro k V σ h0
      rw [Pi.sub_apply, sub_ne_zero] at h0
      exact ⟨(hcv1 k V σ h0).1, hcv3 k V σ h0⟩
    have hAk_fst : ∀ k σ, (∀ V : 𝒱, r.base '' σ.fst.support ≠ closure ({V.1} : Set Y)) →
        Ak k σ = a0 k σ := by
      intro k σ hσ
      simp only [Ak, Pi.add_apply, Finset.sum_apply]
      rw [Finset.sum_eq_zero fun V _ => ?_, add_zero]
      by_contra h0
      exact hσ V (hδ k V σ h0).1
    have hAk_fstV : ∀ k σ (V : 𝒱), r.base '' σ.fst.support = closure ({V.1} : Set Y) →
        Ak k σ = cv k V σ := by
      intro k σ V hV
      simp only [Ak, Pi.add_apply, Finset.sum_apply]
      rw [Finset.sum_eq_single V]
      · simp
      · intro V' _ hV'
        by_contra h0
        exact hV' (Subtype.ext (eq_of_closure_eq ((hδ k V' σ h0).1.symm.trans hV)))
      · simp
    have hAkleg : ∀ k i b, Ak k (leg i b) = (bU k : ∀ i, Br i → ℚ) i b := by
      intro k i b
      rw [hAk_fst k _ (fun V => hleg_fst i b ▸ hst_V i V.1 V.2)]
      simp only [a0, Pi.add_apply, Finset.sum_apply, ha1_leg, Finset.sum_const_zero, add_zero]
      exact he_leg k i b
    have hAko : ∀ k, Ak k ∈ orientedSurfaceCoefficients B := fun k =>
      Submodule.add_mem _ (ha0o k) (Submodule.sum_mem _ fun V _ =>
        Submodule.sub_mem _ (hcvo k V) (ha0o k))
    -- on a strict component, only the legs and the strict corrections contribute
    have he_st : ∀ k i σ, σ.fst = st i →
        e k σ = (∑ b, edgeSystem (leg i b) ((bU k : ∀ i, Br i → ℚ) i b)) σ := by
      intro k i σ hσ
      simp only [e, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · intro j _ hj
        refine Finset.sum_eq_zero fun b _ => edgeSystem_apply_of_ne _ _ _ ?_ ?_
        · intro h0
          apply hj
          apply hst_inj
          rw [← hleg_fst j b, ← h0, hσ]
        · intro h0
          apply hst_F i
          rw [← hσ, h0, DoubleSurface.swap_fst]
          exact hleg_snd j b
      · simp
    have ha1_st : ∀ k i σ, σ.fst = st i → (∑ j, a1 k j) σ = a1 k i σ := by
      intro k i σ hσ
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · intro j _ hj
        by_contra h0
        rcases ((ha1s k j σ h0).1) with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hj (hst_inj (h1.symm.trans hσ))
        · exact hst_F i (hσ ▸ h2)
      · simp
    have hAkcl : ∀ k i, Chow.divisorClass _ (surfaceCoefficientDivisor (Ak k) (st i)) = 0 := by
      intro k i
      have h1 : surfaceCoefficientDivisor (Ak k) (st i) =
          surfaceCoefficientDivisor (e k) (st i) +
            surfaceCoefficientDivisor (∑ j, a1 k j) (st i) := by
        rw [surfaceCoefficientDivisor_congr (a' := a0 k)
          (fun σ hσ => hAk_fst k σ (fun V => hσ ▸ hst_V i V.1 V.2))]
        exact (Zl (st i)).map_add _ _
      rw [h1, surfaceCoefficientDivisor_congr (fun σ hσ => he_st k i σ hσ), hleg_div,
        surfaceCoefficientDivisor_congr (fun σ hσ => ha1_st k i σ hσ), ha1d]
      exact hc k i
    have hAksup : ∀ k σ, Ak k σ ≠ 0 → r.base '' σ.carrier ⊆ Qs := by
      intro k σ hσ
      by_cases hσV : ∃ V : 𝒱, (cv k V - a0 k) σ ≠ 0
      · obtain ⟨V, hV⟩ := hσV
        exact (hδ k V σ hV).2.trans (hVQ _ V.2)
      · push Not at hσV
        have h0 : a0 k σ ≠ 0 := by
          have : Ak k σ = a0 k σ := by
            simp only [Ak, Pi.add_apply, Finset.sum_apply]
            rw [Finset.sum_eq_zero fun V _ => hσV V, add_zero]
          rwa [this] at hσ
        simp only [a0, Pi.add_apply] at h0
        by_cases he : e k σ = 0
        · rw [he, zero_add, Finset.sum_apply] at h0
          obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
          refine subset_trans (Set.image_mono ?_) (hst_Q j)
          rcases (ha1s k j σ hj).1 with ⟨h1, -⟩ | ⟨h2, -⟩
          · exact h1 ▸ (σ.carrier_subset.trans Set.inter_subset_left)
          · exact h2 ▸ (σ.carrier_subset.trans Set.inter_subset_right)
        · obtain ⟨i, b, rfl | rfl⟩ := he_ne k σ he
          · rw [hleg_img]; exact hVQ _ (Vb i b).2
          · rw [DoubleSurface.swap_carrier, hleg_img]; exact hVQ _ (Vb i b).2
    have hAkpush : ∀ k (E : F.support), componentPushforward r E.1 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor (Ak k) E.1)) = 0 := by
      intro k E
      by_cases hEV : ∃ V : 𝒱, r.base '' E.1.support = closure ({V.1} : Set Y)
      · obtain ⟨V, hV⟩ := hEV
        rw [surfaceCoefficientDivisor_congr (a' := cv k V)
          (fun σ hσ => hAk_fstV k σ V (hσ ▸ hV))]
        haveI : IsComplexScheme E.1.idealSheaf.subscheme :=
          IsComplexScheme.of_isClosedImmersion E.1.idealSheaf.subschemeι
        refine rationalCycleGroup_ext fun w => ?_
        rw [map_zero]
        by_cases hW : w = V.1
        · subst hW
          exact hcv2 k V E.1 (hFB E.2) hV
        · by_contra hne
          obtain ⟨x, hxw, -, hw2⟩ :=
            exists_eq_of_rationalCoeff_rationalProperPushforward_ne_zero
              (E.1.idealSheaf.subschemeι ≫ r) _ hne
          have hwV : w ∈ closure ({V.1} : Set Y) := by
            rw [← hV, ← hxw]
            refine ⟨E.1.idealSheaf.subschemeι x, ?_, rfl⟩
            have : E.1.idealSheaf.subschemeι x ∈ Set.range E.1.idealSheaf.subschemeι := ⟨_, rfl⟩
            rwa [E.1.idealSheaf.range_subschemeι] at this
          exact hW (hV2 V.1 w (h𝒱 _ V.2)
            ((relativeDimension_eq_iff_topologicalKrullDim_closure _ w 2).1 hw2)
            (closure_minimal (Set.singleton_subset_iff.2 hwV) isClosed_closure))
      · push Not at hEV
        have hfst : ∀ σ : DoubleSurface B, σ.fst = E.1 → Ak k σ ≠ 0 →
            topologicalKrullDim (r.base '' σ.carrier) ≤ 1 := by
          intro σ hσE hσ
          rw [hAk_fst k σ (fun V => hσE ▸ hEV V)] at hσ
          simp only [a0, Pi.add_apply] at hσ
          by_cases he : e k σ = 0
          · rw [he, zero_add, Finset.sum_apply] at hσ
            obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
            exact (ha1s k j σ hj).2
          · exfalso
            obtain ⟨i, b, rfl | rfl⟩ := he_ne k σ he
            · exact hst_F i (hleg_fst i b ▸ hσE ▸ E.2)
            · apply hEV (Vb i b)
              rw [← hσE, DoubleSurface.swap_fst]
              exact hleg_sndimg i b
        let a' : DoubleSurface B → ℚ := fun σ => if σ.fst = E.1 ∨ σ.snd = E.1 then Ak k σ else 0
        have ha' : a' ∈ verticalSurfaceCoefficients r B := by
          refine ⟨fun σ => ?_, fun σ hσ => ?_⟩
          · show (if σ.swap.fst = E.1 ∨ σ.swap.snd = E.1 then Ak k σ.swap else 0) =
              -(if σ.fst = E.1 ∨ σ.snd = E.1 then Ak k σ else 0)
            by_cases h0 : σ.fst = E.1 ∨ σ.snd = E.1
            · rw [if_pos (show σ.swap.fst = E.1 ∨ σ.swap.snd = E.1 from h0.symm), if_pos h0,
                hAko k σ]
            · rw [if_neg (show ¬ (σ.swap.fst = E.1 ∨ σ.swap.snd = E.1) from
                fun h' => h0 h'.symm), if_neg h0, neg_zero]
          · simp only [a'] at hσ
            split_ifs at hσ with h0
            · rcases h0 with h1 | h2
              · exact hfst σ h1 hσ
              · have := hfst σ.swap h2 (by rw [hAko k σ]; exact neg_ne_zero.2 hσ)
                rwa [DoubleSurface.swap_carrier] at this
            · exact absurd rfl hσ
        rw [surfaceCoefficientDivisor_congr (a' := a')
          (fun σ hσ => by simp only [a', if_pos (Or.inl hσ)])]
        exact rationalProperPushforward_divisorCycle_eq_zero_of_mem_vertical r B ha' E.1
    have hAk : ∀ k, Ak k ∈ Sadm := fun k =>
      ⟨⟨⟨hAko k, Submodule.mem_iInf _ |>.2 fun i => LinearMap.mem_ker.2 (hAkcl k i)⟩,
        hAksup k⟩, Submodule.mem_iInf _ |>.2 fun E => LinearMap.mem_ker.2 (hAkpush k E)⟩
    refine ⟨bU.constr ℚ Ak, fun u => ?_, fun u i b => ?_⟩
    · rw [Module.Basis.constr_apply]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hAk k)
    · rw [Module.Basis.constr_apply_fintype, Finset.sum_apply]
      simp only [Pi.smul_apply, hAkleg, smul_eq_mul]
      conv_rhs => rw [← bU.sum_repr u]
      rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      simp
  -- the classes of an admissible system
  let xmap : (DoubleSurface B → ℚ) →ₗ[ℚ] ComponentHomology F :=
    LinearMap.pi fun E => Chow.divisorClass _ ∘ₗ Zl E.1
  have hx : ∀ a ∈ Sadm, xmap a ∈ verticalKernelOver r F Qs := by
    intro a ha
    obtain ⟨⟨⟨hor, hcl⟩, hsup⟩, hpush⟩ := ha
    rw [verticalKernelOver, mem_exceptionalKernel]
    refine ⟨fun E => ⟨Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1), ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact Submodule.mem_iInf _ |>.1 hpush E
    · intro x hx
      haveI : IsComplexScheme E.1.idealSheaf.subscheme :=
        IsComplexScheme.of_isClosedImmersion E.1.idealSheaf.subschemeι
      obtain ⟨P, hP, rfl⟩ := exists_of_rationalCoeff_divisorCycle_ne_zero _ hx
      change (surfaceCoefficientDivisor a E.1).coeff P ≠ 0 at hP
      rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff] at hP
      obtain ⟨σ, hσ⟩ : ∃ σ : {σ : DoubleSurface B // σ.fst = E.1 ∧
          σ.carrier = closure {E.1.idealSheaf.subschemeι P.genericPoint}}, a σ ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hP (finsum_eq_zero_of_forall_eq_zero hne)
      refine subset_trans ?_ (hsup σ.1 hσ)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, σ.2.2]
      exact Set.image_mono (image_closure_subset_closure_image
        (E.1.idealSheaf.subschemeι.base.hom.continuous) |>.trans (by rw [Set.image_singleton]))
    · have hB := sum_componentHomologyMap_divisorClass_eq_zero' hcoh a hor
      let f : MMP.Mori.PrimeDivisor Z → RationalHomology Z 4 := fun G =>
        componentHomologyMap G 4 (Chow.divisorClass G.idealSheaf.subscheme
          (surfaceCoefficientDivisor a G))
      change ∑ E : F.support, f E.1 = 0
      change ∑ E : B.support, f E.1 = 0 at hB
      rw [Finset.sum_coe_sort F.support f]
      rw [Finset.sum_coe_sort B.support f] at hB
      rw [Finset.sum_subset hFB, hB]
      intro G hGB hGF
      obtain ⟨i, rfl⟩ := hst_cov G hGB hGF
      have := Submodule.mem_iInf _ |>.1 hcl i
      simp only [f]
      rw [show Chow.divisorClass _ (surfaceCoefficientDivisor a (st i)) = 0 from this, map_zero]
  let Φ0 : ↥U →ₗ[ℚ] ↥(verticalKernel r F) := (xmap ∘ₗ A).codRestrict _
    (fun u => verticalKernelOver_le r F Qs (hx _ (hAS u)))
  let Φ1 : ↥U →ₗ[ℚ] VerticalDefect r F := (Submodule.mkQ _) ∘ₗ Φ0
  have hΦ1 : ∀ u, Φ1 u ∈ verticalDefectOver r F Qs := fun u => ⟨Φ0 u, hx _ (hAS u), rfl⟩
  refine ⟨Φ1.codRestrict _ hΦ1, (injective_iff_map_eq_zero _).2 fun u hu => ?_⟩
  have h1 : Φ1 u = 0 := congrArg Subtype.val hu
  have h2 : Φ0 u ∈ (verticalSurfaceClasses r F).comap (verticalKernel r F).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 h1
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ verticalSurfaceCoefficients r F,
      surfaceCoefficientClasses F b = xmap (A u) := h2
  have hFD : F.support ⊆ D.support := hFB.trans hBD
  have hc : extendCoeff hBD (A u) - extendCoeff hFD b = 0 := by
    refine eq_zero_of_mem_verticalSurfaceCoefficients_of_surfaceCoefficientClasses_eq_zero sX
      (r ≫ p) hcompX hf hZ hdim D hDsnc hDpos hA ?_ ?_
    · have hAu := hAS u
      obtain ⟨⟨⟨hor, -⟩, hsup⟩, -⟩ := hAu
      refine ⟨Submodule.sub_mem _ (extendCoeff_mem_orientedSurfaceCoefficients hBD hor)
        (extendCoeff_mem_orientedSurfaceCoefficients hFD hb.1), fun σ hσ => ?_⟩
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      by_cases ha : extendCoeff hBD (A u) σ = 0
      · have hb' : extendCoeff hFD b σ ≠ 0 := by
          intro h0
          apply hσ
          rw [Pi.sub_apply, ha, h0, sub_zero]
        obtain ⟨τ, rfl, hτ⟩ := exists_eq_ofSubset_of_extendCoeff_ne_zero hFD hb'
        exact hpdim _ (hrc _ (isClosed_carrier τ)) (hb.2 τ hτ)
      · obtain ⟨τ, rfl, hτ⟩ := exists_eq_ofSubset_of_extendCoeff_ne_zero hBD ha
        exact (topologicalKrullDim_mono' (Set.image_mono (hsup τ hτ))).trans hpQ
    · funext G
      obtain ⟨G, hGD⟩ := G
      rw [surfaceCoefficientClasses_apply, Pi.zero_apply]
      change Chow.divisorClass _ (surfaceCoefficientDivisorLinearMap D G
        (extendCoeff hBD (A u) - extendCoeff hFD b)) = 0
      rw [map_sub]
      change Chow.divisorClass _ (surfaceCoefficientDivisor (extendCoeff hBD (A u)) G -
        surfaceCoefficientDivisor (extendCoeff hFD b) G) = 0
      by_cases hGF : G ∈ F.support
      · rw [surfaceCoefficientDivisor_extendCoeff_of_mem hBD _ (hFB hGF),
          surfaceCoefficientDivisor_extendCoeff_of_mem hFD _ hGF, map_sub]
        have := congrFun hbx ⟨G, hGF⟩
        rw [surfaceCoefficientClasses_apply] at this
        rw [this]
        exact sub_self _
      · rw [surfaceCoefficientDivisor_extendCoeff_of_notMem hFD _ hGF, sub_zero]
        by_cases hGB : G ∈ B.support
        · rw [surfaceCoefficientDivisor_extendCoeff_of_mem hBD _ hGB]
          obtain ⟨i, rfl⟩ := hst_cov G hGB hGF
          obtain ⟨⟨⟨-, hcl⟩, -⟩, -⟩ := hAS u
          exact Submodule.mem_iInf _ |>.1 hcl i
        · rw [surfaceCoefficientDivisor_extendCoeff_of_notMem hBD _ hGB, map_zero]
  refine Subtype.ext (funext fun i => funext fun b' => ?_)
  have h3 := congrFun hc (ofSubset hBD (leg i b'))
  rw [Pi.sub_apply, extendCoeff_apply_ofSubset, hAleg, Pi.zero_apply] at h3
  have h4 : extendCoeff hFD b (ofSubset hBD (leg i b')) = 0 := by
    change (if h : (leg i b').fst ∈ F.support ∧ (leg i b').snd ∈ F.support then _ else 0) = 0
    rw [dif_neg fun h => hst_F i (hleg_fst i b' ▸ h.1)]
  rw [h4, sub_zero] at h3
  exact h3

end Injection

/-! ### The key inequality on the simultaneous model -/

section Key

open MMP MMP.Fourfold.ConductorBlowup
open scoped MMP.SubschemeOver

private lemma genericPoint_mem_support' {X : Scheme.{0}} (G : MMP.Mori.PrimeDivisor X) :
    G.genericPoint ∈ (G.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A prime divisor whose support lies in the support of a divisor is one of its components. -/
private lemma mem_support_of_support_subset_supp {X : Scheme.{0}} {B : Divisor X}
    {G : MMP.Mori.PrimeDivisor X} (h : (G.support : Set X) ⊆ B.supp) : G ∈ B.support := by
  rw [ConductorBlowup.coe_supp_eq_iUnion] at h
  obtain ⟨P, hP, hGP⟩ := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun P _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P)
    (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support G) h
  rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hGP]

/-- A component of a divisor has support in the support of the divisor. -/
private lemma support_subset_supp_of_mem {X : Scheme.{0}} {B : Divisor X}
    {G : MMP.Mori.PrimeDivisor X} (h : G ∈ B.support) : (G.support : Set X) ⊆ B.supp :=
  DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 h)

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private lemma isBirationalMorphism_comp' {V X' X : Scheme.{0}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rw [hfac]; exact h1
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- On a smooth complex scheme every stalk has a regular system of parameters. -/
private lemma exists_isRegularSystemOfParameters_of_isSmoothScheme {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]
    (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) (y : Z) :
    ∃ (n : ℕ) (z : Fin n → Z.presheaf.stalk y), MMP.Mori.IsRegularSystemOfParameters z := by
  haveI : Smooth (Z ↘ Spec (.of ℂ)) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field (Z ↘ Spec (.of ℂ)) y
  exact MMP.Mori.exists_isRegularSystemOfParameters _

/-- A pure codimension-one closed subset of an snc closed subset of a smooth complex scheme is
the support of a reduced snc divisor. -/
private lemma exists_reducedDivisor_of_subset {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [NoetherianSpace Z] [IsLocallyNoetherian Z] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]
    (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ))) {T D : Set Z}
    (hD : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) D) (hT : IsClosed T)
    (hTp : IsPureCodimOne (⟨T, hT⟩ : Closeds Z)) (hsub : T ⊆ D) :
    ∃ B : Divisor Z, MMP.Intersection.IsReducedEffective B ∧
      DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) B ∧ (B.supp : Set Z) = T :=
  ConductorBlowup.exists_divisor_of_subset _
    (exists_isRegularSystemOfParameters_of_isSmoothScheme hsm) hD hT hTp hsub

/-- An snc closed subset is pure of codimension one. -/
private lemma isPureCodimOne_of_isSNCClosedSubset {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    {D : Set Z} (hD : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) D) :
    IsPureCodimOne (⟨D, hD.1⟩ : Closeds Z) := by
  rcases hD.2 with h | h
  · intro W hW
    exfalso
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    have hwD : w ∈ D := hW.1 hw
    rw [h] at hwD
    exact hwD
  · exact h.1

/-- A closed birational morphism onto an irreducible scheme is surjective. -/
private lemma surjective_of_isBirationalMorphism {Z Y : Scheme.{0}} [Nonempty Z]
    [IrreducibleSpace Y] (r : Z ⟶ Y) (hrc : IsClosedMap r.base)
    (hbir : MMP.Mori.IsBirationalMorphism r) : Function.Surjective r.base := by
  obtain ⟨W, hWne, hW⟩ := hbir.exists_isOpenImmersion
  have hopen : IsOpen (Set.range (W.ι ≫ r).base) := (W.ι ≫ r).isOpenEmbedding.isOpen_range
  have hne : (Set.range (W.ι ≫ r).base).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    exact ⟨_, ⟨⟨w, hw⟩, rfl⟩⟩
  have hsub : Set.range (W.ι ≫ r).base ⊆ Set.range r.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨_, rfl⟩
  have hcl : IsClosed (Set.range r.base) := by
    rw [← Set.image_univ]
    exact hrc _ isClosed_univ
  intro y
  have h1 : closure (Set.range (W.ι ≫ r).base) ⊆ Set.range r.base := closure_minimal hsub hcl
  rw [(hopen.dense hne).closure_eq] at h1
  exact h1 (Set.mem_univ y)

section IsoOver

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} [IsIso (f ∣_ U)]

private lemma isOpenEmbedding_ι_comp_of_isIso_restrict :
    Topology.IsOpenEmbedding ((f ⁻¹ᵁ U).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  exact Scheme.Hom.isOpenEmbedding _

private lemma exists_ι_eq_of_mem {q : X} (hq : f q ∈ U) : ∃ z : (f ⁻¹ᵁ U).toScheme,
    (f ⁻¹ᵁ U).ι z = q := by
  have : q ∈ Set.range (f ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hq
  exact this

/-- Over an open on which `f` restricts to an isomorphism, every point has a preimage. -/
private lemma exists_apply_eq_of_isIso_restrict {y : Y} (hy : y ∈ U) : ∃ q, f q = y := by
  have hrange : y ∈ Set.range ((f ∣_ U) ≫ U.ι) := by
    have hsurj : Function.Surjective (f ∣_ U) := fun w =>
      ⟨inv (f ∣_ U) w, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    exact hy
  obtain ⟨q, hq⟩ := hrange
  rw [morphismRestrict_ι] at hq
  exact ⟨_, hq⟩

/-- Over an open on which `f` restricts to an isomorphism, `f` reflects specialization. -/
private lemma specializes_iff_of_isIso_restrict {q q' : X} (hq : f q ∈ U) (hq' : f q' ∈ U) :
    q ⤳ q' ↔ f q ⤳ f q' := by
  obtain ⟨z, rfl⟩ := exists_ι_eq_of_mem f hq
  obtain ⟨z', rfl⟩ := exists_ι_eq_of_mem f hq'
  have h := (isOpenEmbedding_ι_comp_of_isIso_restrict f (U := U)).isInducing.specializes_iff
    (x := z) (y := z')
  have h' := (f ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.specializes_iff (x := z) (y := z')
  rw [h']
  exact h.symm

end IsoOver

/-- A strict generization of the generic point of a prime divisor of an irreducible scheme is the
generic point of the scheme. -/
private lemma eq_genericPoint_of_specializes {Y : Scheme.{0}} [IrreducibleSpace Y]
    (S : MMP.Mori.PrimeDivisor Y) {w : Y} (hw : w ⤳ S.genericPoint) (hne : w ≠ S.genericPoint) :
    w = genericPoint Y := by
  have hle : S.genericPoint ≤ w := hw
  have hlt : S.genericPoint < w :=
    lt_iff_le_not_ge.mpr ⟨hle, fun h' =>
      hne (Specializes.antisymm (h' : S.genericPoint ⤳ w) hw).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt
  rw [S.coheight_genericPoint] at h1
  have h0 : Order.coheight w = 0 := by
    revert h1
    induction Order.coheight w using ENat.recTopCoe with
    | top => intro h1; simp at h1
    | coe n =>
      intro h1
      have : n + 1 ≤ 1 := by exact_mod_cast h1
      have : n = 0 := by omega
      simp [this]
  rw [Order.coheight_eq_zero] at h0
  have hgen : w ≤ genericPoint Y := (genericPoint_spec Y).specializes (Set.mem_univ w)
  have h2 : genericPoint Y ≤ w := h0 hgen
  exact (Specializes.antisymm (h2 : w ⤳ genericPoint Y) (hgen : genericPoint Y ⤳ w)).eq

/-- The generic point of an irreducible scheme lies in no prime divisor. -/
private lemma genericPoint_notMem_support {Y : Scheme.{0}} [IrreducibleSpace Y]
    (S : MMP.Mori.PrimeDivisor Y) : genericPoint Y ∉ (S.support : Set Y) := by
  intro h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hsp : S.genericPoint ⤳ genericPoint Y := specializes_iff_mem_closure.2 h
  have hge : genericPoint Y ⤳ S.genericPoint :=
    (genericPoint_spec Y).specializes (Set.mem_univ _)
  have heq : S.genericPoint = genericPoint Y := (Specializes.antisymm hsp hge).eq
  have hmax : IsMax S.genericPoint := by
    intro b _
    rw [heq]
    exact (genericPoint_spec Y).specializes (Set.mem_univ b)
  have h1 := S.coheight_genericPoint
  rw [Order.coheight_eq_zero.2 hmax] at h1
  exact absurd h1 (by decide)

/-- **The strict components.** Every component `S` of `Q` has a unique component of `B` over
its generic point which is not exceptional for `r`; these are exactly the non-exceptional
components of `B`. -/
private lemma exists_strictComponents {Y Z : Scheme.{0}} [IsIntegral Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (hYv : AlgebraicGeometry.IsVariety ℂ sY) (r : Z ⟶ Y) [IsProper r]
    (hZv : AlgebraicGeometry.IsVariety ℂ (r ≫ sY)) (hbir : MMP.Mori.IsBirationalMorphism r)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) (Qs : Set Y)
    (hQs : Qs = ⋃ S ∈ Q, (S.support : Set Y)) (B F : Divisor Z)
    (hBsupp : (B.supp : Set Z) = r.base ⁻¹' Qs ∪ exceptionalSet r)
    (hFsupp : (F.supp : Set Z) = exceptionalSet r) :
    ∃ st : Q → MMP.Mori.PrimeDivisor Z, Function.Injective st ∧ (∀ S, st S ∈ B.support) ∧
      (∀ S, st S ∉ F.support) ∧ (∀ S, (st S).genericPoint ∉ exceptionalSet r) ∧
      (∀ G ∈ B.support, G ∉ F.support → ∃ S, st S = G) ∧
      (∀ S, r.base (st S).genericPoint = (S : MMP.Mori.PrimeDivisor Y).genericPoint) ∧
      ∀ S, IsIso (r.stalkMap (st S).genericPoint) := by
  classical
  set V := biregularLocus r
  haveI : IsIso (r ∣_ V) := isBiregular_biregularLocus r
  have hcod := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sY r (hY := hYv) (hX := hZv)
    hbir
  have hηV : ∀ S : Q, (S : MMP.Mori.PrimeDivisor Y).genericPoint ∈ V := fun S => by
    by_contra h
    have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcod _ h
    rw [S.1.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hYQ : genericPoint Y ∉ Qs := by
    rw [hQs]
    intro h
    obtain ⟨S, -, hS⟩ := Set.mem_iUnion₂.1 h
    exact genericPoint_notMem_support S hS
  have hex : ∀ S : Q, ∃ G ∈ B.support,
      r.base G.genericPoint = (S : MMP.Mori.PrimeDivisor Y).genericPoint := by
    intro S
    obtain ⟨z, hz⟩ := exists_apply_eq_of_isIso_restrict r (hηV S)
    have hzB : z ∈ (B.supp : Set Z) := by
      rw [hBsupp]
      left
      change r.base z ∈ Qs
      rw [hz, hQs]
      exact Set.mem_biUnion S.2 (genericPoint_mem_support' S.1)
    rw [ConductorBlowup.coe_supp_eq_iUnion] at hzB
    obtain ⟨G, hG, hzG⟩ := Set.mem_iUnion₂.1 hzB
    refine ⟨G, hG, ?_⟩
    have hsp : G.genericPoint ⤳ z := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzG
      exact specializes_iff_mem_closure.2 hzG
    have hsp' : r.base G.genericPoint ⤳ (S : MMP.Mori.PrimeDivisor Y).genericPoint :=
      hz ▸ hsp.map r.base.hom.continuous
    by_contra hne
    have hgY := eq_genericPoint_of_specializes S.1 hsp' hne
    have hGV : r.base G.genericPoint ∈ V := hsp'.mem_open V.isOpen (hηV S)
    have hGB : G.genericPoint ∈ (B.supp : Set Z) :=
      support_subset_supp_of_mem hG (genericPoint_mem_support' G)
    rw [hBsupp] at hGB
    rcases hGB with h1 | h1
    · exact hYQ (hgY ▸ h1)
    · exact h1 hGV
  choose st hstB hstgen using hex
  have hstV : ∀ S, r.base (st S).genericPoint ∈ V := fun S => (hstgen S).symm ▸ hηV S
  have hst_ex : ∀ S, (st S).genericPoint ∉ exceptionalSet r := fun S h => h (hstV S)
  have hst_F : ∀ S, st S ∉ F.support := fun S h => hst_ex S (by
    have := support_subset_supp_of_mem h (genericPoint_mem_support' _)
    rwa [hFsupp] at this)
  refine ⟨st, fun S S' h => ?_, hstB, hst_F, hst_ex, fun G hG hGF => ?_, hstgen,
    fun S => isIso_stalkMap_of_isIso_morphismRestrict r (U := V) inferInstance (hstV S)⟩
  · have := hstgen S
    rw [h, hstgen S'] at this
    exact Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective this.symm)
  · have hGex : G.genericPoint ∉ exceptionalSet r := by
      intro h
      apply hGF
      refine mem_support_of_support_subset_supp ?_
      rw [hFsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_minimal (Set.singleton_subset_iff.2 h) (exceptionalSet r).isClosed
    have hGV : r.base G.genericPoint ∈ V := not_not.1 hGex
    have hGB : G.genericPoint ∈ (B.supp : Set Z) :=
      support_subset_supp_of_mem hG (genericPoint_mem_support' G)
    rw [hBsupp] at hGB
    have hGQ : r.base G.genericPoint ∈ Qs := by
      rcases hGB with h1 | h1
      · exact h1
      · exact absurd h1 hGex
    rw [hQs] at hGQ
    obtain ⟨S, hS, hGS⟩ := Set.mem_iUnion₂.1 hGQ
    refine ⟨⟨S, hS⟩, (ConductorBlowup.eq_of_genericPoint_mem_support ?_).symm⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
      specializes_iff_of_isIso_restrict r (hstV ⟨S, hS⟩) hGV, hstgen]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hGS
    exact specializes_iff_mem_closure.2 hGS

section Normalization

variable {Y : Scheme.{0}} (P : MMP.Mori.PrimeDivisor Y)

/-- The closed subscheme of a prime divisor of a variety is a variety. -/
private lemma isVariety_subschemeι' (s : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ s] :
    AlgebraicGeometry.IsVariety ℂ (P.idealSheaf.subschemeι ≫ s) := by
  have := P.integral
  have : IsSeparated s := inferInstance
  have : LocallyOfFiniteType s := inferInstance
  have : QuasiCompact s := inferInstance
  exact {}

/-- The normalization of a prime divisor of a variety is finite over the variety. -/
private lemma isFinite_primeDivisorNormalization' (s : Y ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ s] : IsFinite (primeDivisorNormalization P) := by
  have := P.integral
  have := isVariety_subschemeι' P s
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization P.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType _ (P.idealSheaf.subschemeι ≫ s) _
  exact inferInstanceAs (IsFinite (_ ≫ _))

/-- The normalization of a prime divisor of a variety is integral. -/
private lemma isIntegral_primeDivisorNormalizationScheme' :
    IsIntegral (primeDivisorNormalizationScheme P) := by
  have := P.integral
  exact Scheme.isIntegral_normalizationScheme _
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

/-- The normalization of a prime divisor of a variety is a variety. -/
private lemma isVariety_primeDivisorNormalization' (s : Y ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ s] :
    AlgebraicGeometry.IsVariety ℂ (primeDivisorNormalization P ≫ s) := by
  have := isFinite_primeDivisorNormalization' P s
  have := isIntegral_primeDivisorNormalizationScheme' P
  have : IsSeparated s := inferInstance
  have : LocallyOfFiniteType s := inferInstance
  have : QuasiCompact s := inferInstance
  exact {}

/-- The normalization of a prime divisor of a projective variety over `ℂ` is a projective
variety: it is finite over the variety. -/
private lemma isProjectiveVariety_primeDivisorNormalization' (s : Y ⟶ Spec (.of ℂ))
    (hs : AlgebraicGeometry.IsProjectiveVariety ℂ s) :
    AlgebraicGeometry.IsProjectiveVariety ℂ (primeDivisorNormalization P ≫ s) := by
  have := isFinite_primeDivisorNormalization' P s
  have := isVariety_primeDivisorNormalization' P s
  exact (isProjectiveVariety_iff_isProjective ℂ _).mpr
    ((Stacks.FiniteMorphismProjective.isProjective_of_isFinite _).comp
      hs.isProjective.isProjective)

end Normalization

section Lift

/-- If `h ≫ ν = ι ≫ r` with `r` inducing an isomorphism and `ι` a surjection of stalks at `x`,
and the stalk of the target of `h` at `h x` is a field, then `h` induces an isomorphism of
stalks at `x`. -/
private lemma isIso_stalkMap_of_comp_eq {M N Z Y : Scheme.{0}} (h : M ⟶ N) (ν : N ⟶ Y)
    (ι : M ⟶ Z) (r : Z ⟶ Y) (hcomm : h ≫ ν = ι ≫ r) (x : M) (hr : IsIso (r.stalkMap (ι x)))
    (hι : Function.Surjective (ι.stalkMap x)) (hN : IsField (N.presheaf.stalk (h x)))
    [Nontrivial (M.presheaf.stalk x)] : IsIso (h.stalkMap x) := by
  have e := Scheme.Hom.stalkMap_congr_hom _ _ hcomm x
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
  have hsurj : Function.Surjective (ν.stalkMap (h x) ≫ h.stalkMap x) := by
    rw [e]
    exact (hι.comp (ConcreteCategory.bijective_of_isIso (r.stalkMap (ι x))).2).comp
      (Iso.commRingCatIsoToRingEquiv _).surjective
  letI := hN.toField
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨(h.stalkMap x).hom.injective, Function.Surjective.of_comp hsurj⟩

private lemma eq_of_le_of_comap_eq_of_isIntegral' {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) {P Q : Ideal S} [P.IsPrime] (hPQ : P ≤ Q)
    (h : P.comap φ = Q.comap φ) : P = Q := by
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hφ⟩
  by_contra hne
  exact (Ideal.IsIntegral.comap_lt_comap (R := R) (lt_of_le_of_ne hPQ hne)).ne h

private lemma eq_of_specializes_of_isIntegral_specMap' {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : φ.hom.IsIntegral) (p q : PrimeSpectrum S) (hpq : p ⤳ q)
    (hc : Spec.map φ p = Spec.map φ q) : p = q := by
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  exact PrimeSpectrum.ext (eq_of_le_of_comap_eq_of_isIntegral' _ hφ hpq
    (congrArg PrimeSpectrum.asIdeal hc))

private lemma eq_of_specializes_of_isIntegralHom_of_isAffine' {X Z : Scheme.{0}} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Z) [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') :
    t = t' := by
  have hg : (f.appTop).hom.IsIntegral := f.isIntegral_app ⊤ (isAffineOpen_top Z)
  have hc : (Spec.map f.appTop) (X.isoSpec.hom t) = (Spec.map f.appTop) (X.isoSpec.hom t') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, he]
  have heq := congrArg X.isoSpec.inv (eq_of_specializes_of_isIntegral_specMap' _ hg _ _
    (h.map X.isoSpec.hom.continuous) hc)
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at heq

/-- **Incomparability.** The fibres of an integral morphism carry no nontrivial
specializations. -/
private lemma eq_of_specializes_of_isIntegralHom' {X Z : Scheme.{0}} (f : X ⟶ Z)
    [IsIntegralHom f] {t t' : X} (h : t ⤳ t') (he : f t = f t') : t = t' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t')) isOpen_univ
  have ht' : t' ∈ f ⁻¹ᵁ U := hmem
  have ht : t ∈ f ⁻¹ᵁ U := h.mem_open (f ⁻¹ᵁ U).isOpen ht'
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  let a : (f ⁻¹ᵁ U).toScheme := ⟨t, ht⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨t', ht'⟩
  have hab : a ⤳ b := subtype_specializes_iff _ _ |>.2 h
  have hfab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext
    ((morphismRestrict_base_coe f U a).trans (he.trans (morphismRestrict_base_coe f U b).symm))
  exact congrArg Subtype.val (eq_of_specializes_of_isIntegralHom_of_isAffine' (f ∣_ U) hab hfab)

/-- A morphism from a projective `k`-variety to a `k`-variety, over `k`, is projective. -/
private lemma isProjectiveMorphism_of_comp_eq' {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : AlgebraicGeometry.IsVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjectiveMorphism f := by
  have : IsSeparated sY := hY.toIsSeparated
  let γ : X ⟶ Limits.pullback sX sY := Limits.pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (Limits.pullback.fst sX sY) inferInstance
      (by simp only [γ, Limits.pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ Limits.pullback.snd sX sY = f := Limits.pullback.lift_snd _ _ _
  rw [← hγ]
  exact (MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)

/-- **The strict transform maps to the normalization.** A prime divisor `E` of `Z`, normal and
projective, over a prime divisor `S` of `Y` along `r` with `r` an isomorphism of local rings at
the generic point of `E`, lifts to a projective birational morphism `E ⟶ S^ν` over `ℂ`. -/
private lemma exists_lift_primeDivisorNormalization_of_strict {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) (S : MMP.Mori.PrimeDivisor Y) (E : MMP.Mori.PrimeDivisor Z)
    (r : Z ⟶ Y) (hEimg : r.base '' E.support ⊆ S.support)
    (hEgen : r.base E.genericPoint = S.genericPoint)
    (hEiso : IsIso (r.stalkMap E.genericPoint))
    [E.idealSheaf.subscheme.Over (Spec (.of ℂ))] [IsNormal E.idealSheaf.subscheme]
    (hcomp : E.idealSheaf.subschemeι ≫ r ≫ sY = E.idealSheaf.subscheme ↘ Spec (.of ℂ))
    (hM : MMP.Mori.IsProjectiveVariety ℂ (E.idealSheaf.subscheme ↘ Spec (.of ℂ)))
    (hN : AlgebraicGeometry.IsVariety ℂ (primeDivisorNormalization S ≫ sY)) :
    letI := primeDivisorNormalizationOver sY S
    ∃ h : E.idealSheaf.subscheme ⟶ primeDivisorNormalizationScheme S,
      h ≫ primeDivisorNormalization S = E.idealSheaf.subschemeι ≫ r ∧
        h.IsOver (Spec (.of ℂ)) ∧ IsProjectiveMorphism h ∧ MMP.Mori.IsBirationalMorphism h := by
  letI := primeDivisorNormalizationOver sY S
  haveI := S.integral
  haveI := E.integral
  have hS : ∀ U : S.idealSheaf.subscheme.Opens, IsCompact (U : Set S.idealSheaf.subscheme) →
      (irreducibleComponents (U : Set S.idealSheaf.subscheme)).Finite :=
    fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U
  obtain ⟨g₀, hg₀⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    S.idealSheaf (E.idealSheaf.subschemeι ≫ r)).2 (by
      rintro _ ⟨x, rfl⟩
      refine hEimg ⟨E.idealSheaf.subschemeι x, ?_, rfl⟩
      have : E.idealSheaf.subschemeι x ∈ Set.range E.idealSheaf.subschemeι := ⟨x, rfl⟩
      rwa [E.idealSheaf.range_subschemeι] at this)
  have hg₀gen : g₀ (genericPoint E.idealSheaf.subscheme) = genericPoint S.idealSheaf.subscheme := by
    apply S.idealSheaf.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hg₀, Scheme.Hom.comp_apply]
    exact hEgen
  set N' := S.idealSheaf.subscheme.normalizationScheme hS
  set ν' : N' ⟶ S.idealSheaf.subscheme := S.idealSheaf.subscheme.normalization hS
  obtain ⟨h, hh, -⟩ := Scheme.existsUnique_lift_normalization hS g₀ (fun ⟨x, hx⟩ => by
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      change g₀ x ∈ genericPoints S.idealSheaf.subscheme
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff, hx]
      exact hg₀gen)
  have hcomm : h ≫ (ν' ≫ S.idealSheaf.subschemeι) = E.idealSheaf.subschemeι ≫ r := by
    rw [← Category.assoc, hh, hg₀]
  have hover : h ≫ ((ν' ≫ S.idealSheaf.subschemeι) ≫ sY) =
      E.idealSheaf.subscheme ↘ Spec (.of ℂ) := by
    rw [← Category.assoc, hcomm, Category.assoc]
    exact hcomp
  have hN' : AlgebraicGeometry.IsVariety ℂ ((ν' ≫ S.idealSheaf.subschemeι) ≫ sY) := hN
  have hproj : IsProjectiveMorphism h := isProjectiveMorphism_of_comp_eq' hM hN' hover
  -- the generic point goes to the generic point
  haveI : IsIntegral N' := Scheme.isIntegral_normalizationScheme _ hS
  haveI : IsNormal N' := Scheme.isNormal_normalizationScheme _ hS
  haveI : IsIntegralHom ν' := Scheme.isIntegralHom_normalization _ hS
  have hηN : h (genericPoint E.idealSheaf.subscheme) = genericPoint N' := by
    refine (eq_of_specializes_of_isIntegralHom' ν'
      ((genericPoint_spec _).specializes (Set.mem_univ _)) ?_).symm
    rw [← Scheme.Hom.comp_apply, hh, hg₀gen,
      IsBirational.genericPoint_eq _ (Scheme.isBirational_normalization _ hS)]
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hproj
  haveI : Surjective h := ⟨fun y => by
    have hcl : IsClosed (Set.range h.base) := by
      rw [← Set.image_univ]
      exact h.isClosedMap _ isClosed_univ
    have hsub : closure {genericPoint N'} ⊆ Set.range h.base :=
      closure_minimal (by rintro _ rfl; exact ⟨_, hηN⟩) hcl
    rw [genericPoint_closure] at hsub
    exact hsub (Set.mem_univ y)⟩
  haveI : IsIso (h.stalkMap (genericPoint E.idealSheaf.subscheme)) :=
    isIso_stalkMap_of_comp_eq h (ν' ≫ S.idealSheaf.subschemeι) E.idealSheaf.subschemeι r hcomm _
      hEiso (SurjectiveOnStalks.stalkMap_surjective _ _)
      (by rw [hηN]; exact Field.toIsField N'.functionField)
  have hbir' : IsBirational h := isBirational_of_isIso_stalkMap_genericPoint h
  haveI : LocallyOfFiniteType ((ν' ≫ S.idealSheaf.subschemeι) ≫ sY) := hN'.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N' :=
    LocallyOfFiniteType.isLocallyNoetherian ((ν' ≫ S.idealSheaf.subschemeι) ≫ sY)
  have hbir := MMP.Mori.isBirationalMorphism_comp_of_isBirational (𝟙 N') h
    (isBirational_of_isIso_stalkMap_genericPoint (𝟙 _)) hbir'
  rw [Category.comp_id] at hbir
  exact ⟨h, hcomm, ⟨hover⟩, hproj, hbir⟩

end Lift

/-- A surface with more than one branch has finitely many branches on each component. -/
private lemma finite_branches_of_one_lt {Y : Scheme.{0}} (Q : Finset (MMP.Mori.PrimeDivisor Y))
    {V : Set Y} (hV : 1 < boundaryBranchCount Q V) (S : MMP.Mori.PrimeDivisor Y) (hS : S ∈ Q) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support = V}.Finite := by
  have hfin : {P : (S : Q) × MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
      primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V}.Finite :=
    Set.finite_of_ncard_pos (by unfold boundaryBranchCount at hV; omega)
  refine (hfin.preimage (f := fun P => (⟨⟨S, hS⟩, P⟩ : (S : Q) × MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)))) ?_).subset ?_
  · intro P _ P' _ h
    simpa using h
  · intro P hP
    exact hP

section Rho

open MMP MMP.UnderlyingSpace

/-- Push-forward along a homeomorphism is bijective. -/
private lemma bijective_pushforward_of_homeomorph' {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (hg : IsProperMap g) (e : Y' ≃ₜ Y) (he : ∀ x, g x = e x) (k : ℤ) :
    Function.Bijective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg k).hom := by
  let g' : Y ⟶ Y' := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hg' : IsProperMap g' := e.symm.isProperMap
  have hid : ∀ {Z : TopCat.{0}} (u : Z ⟶ Z) (hu : IsProperMap u) (_ : u = 𝟙 Z) x,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) u hu k).hom x = x := by
    intro Z u hu h x
    subst h
    rw [borelMooreHomology.pushforward_id]
    rfl
  refine Function.bijective_iff_has_inverse.2
    ⟨(borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g' hg' k).hom, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    exact hid _ _ (TopCat.ext fun y ↦ by
      change e.symm (g y) = y
      rw [he, e.symm_apply_apply]) x
  · rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]
    exact hid _ _ (TopCat.ext fun y ↦ by
      change g (e.symm y) = y
      rw [he, e.apply_symm_apply]) x

/-- **Divisor classes and the divisor cycle rank.** On a projective complex scheme the span of
the classes of prime divisors in `H_4` has dimension at most `ρ_*`, and is finite-dimensional. -/
private lemma finrank_divisorClasses_le_divisorCycleRank (N : Scheme.{0}) [N.Over (Spec (.of ℂ))]
    [IsComplexScheme N] (hN : IsProjective (N ↘ Spec (.of ℂ))) :
    FiniteDimensional ℚ (divisorClasses N) ∧
      Module.finrank ℚ (divisorClasses N) ≤ MMP.Analytic.divisorCycleRank N := by
  haveI := (MMP.Analytic.finiteDimensional_singularHomology_of_isProjective N hN).2.1 2
  let e := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := N)
  let φ : RationalHomology N 4 →ₗ[ℚ] MMP.Analytic.borelMooreHomology (N ↘ Spec (.of ℂ)) (2 * 2) :=
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, e.symm.continuous⟩) e.symm.isProperMap ((2 * 2 : ℕ) : ℤ)).hom
  have hφ : Function.Injective φ :=
    (bijective_pushforward_of_homeomorph' _ _ e.symm (fun _ => rfl) _).1
  have hle : (divisorClasses N).map φ ≤ MMP.Analytic.cycleSpan N 2 := by
    rw [divisorClasses_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨P, rfl⟩, rfl⟩
    change φ (Chow.divisorClass N (Finsupp.single P 1)) ∈ _
    by_cases h2 : δ[N] P.genericPoint = 2
    · rw [Chow.divisorClass_single h2]
      exact MMP.Analytic.fundamentalClass_mem_cycleSpan P.genericPoint h2
    · rw [Chow.divisorClass, LinearMap.comp_apply, Chow.divisorCycle_single, one_smul,
        Chow.primeDivisorCycle, dif_neg h2, map_zero, map_zero]
      exact Submodule.zero_mem _
  have hinj : Function.Injective ((φ.domRestrict (divisorClasses N)).codRestrict
      (MMP.Analytic.cycleSpan N 2) fun x => hle ⟨x.1, x.2, rfl⟩) := by
    intro x y hxy
    exact Subtype.ext (hφ (congrArg Subtype.val hxy))
  exact ⟨FiniteDimensional.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end Rho

/-- **Double surfaces of an snc divisor.** On a fourfold, a point of dimension at least two lying
on two distinct components of an snc divisor is the generic point of a double surface. -/
private lemma exists_doubleSurface_of_mem_of_isSNC {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X]
    [NoetherianSpace X] (hX : topologicalKrullDim X = 4) {B : Divisor X}
    (hBsnc : DivisorWithCoeffs.IsSNC (X ↘ Spec (.of ℂ)) B) {E₁ E₂ : MMP.Mori.PrimeDivisor X}
    (h₁ : E₁ ∈ B.support) (h₂ : E₂ ∈ B.support) (hne : E₁ ≠ E₂) {y : X}
    (hy₁ : y ∈ E₁.support) (hy₂ : y ∈ E₂.support)
    (hy : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({y} : Set X))) :
    ∃ σ : DoubleSurface B, σ.fst = E₁ ∧ σ.snd = E₂ ∧ σ.carrier = closure {y} := by
  let σ : DoubleSurface B := ⟨E₁, E₂, h₁, h₂, hne,
    connectedComponentIn ((E₁.support : Set X) ∩ E₂.support) y, ⟨y, ⟨hy₁, hy₂⟩, rfl⟩⟩
  have hTirr : IsIrreducible σ.carrier := ConductorBlowup.isIrreducible_carrier _ hBsnc σ
  have hTcl : IsClosed σ.carrier := ConductorBlowup.isClosed_connectedComponentIn
    (E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed) y
  have hyT : closure {y} ⊆ σ.carrier :=
    closure_minimal (Set.singleton_subset_iff.2 (mem_connectedComponentIn ⟨hy₁, hy₂⟩)) hTcl
  have hTE : σ.carrier ⊆ (E₁.support : Set X) := σ.carrier_subset.trans Set.inter_subset_left
  have hE₁irr : IsIrreducible (E₁.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hTne : σ.carrier ≠ (E₁.support : Set X) := by
    intro h
    have hg : E₁.genericPoint ∈ σ.carrier := by
      rw [h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    exact hne (ConductorBlowup.eq_of_genericPoint_mem_support (σ.carrier_subset hg).2)
  have hE3 := ConductorBlowup.topologicalKrullDim_support_eq_three hX E₁
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hE₁irr hTcl hTE hTne
    (by rw [hE3]; simp; decide)
  rw [hE3] at hlt
  have hle : topologicalKrullDim σ.carrier ≤ ((2 : ℕ) : WithBot ℕ∞) :=
    ConductorBlowup.withBot_le_of_lt_succ (n := 2) hlt
  have hcy : topologicalKrullDim (closure ({y} : Set X)) ≤ topologicalKrullDim σ.carrier :=
    (Topology.IsEmbedding.inclusion hyT).isInducing.topologicalKrullDim_le
  have h2 : topologicalKrullDim (closure ({y} : Set X)) = ((2 : ℕ) : WithBot ℕ∞) :=
    le_antisymm (hcy.trans hle) (by exact_mod_cast hy)
  have hT2 : topologicalKrullDim σ.carrier = ((2 : ℕ) : WithBot ℕ∞) :=
    le_antisymm hle (h2 ▸ hcy)
  have heq := ConductorBlowup.eq_of_subset_of_topologicalKrullDim_eq (d := 4)
    (by rw [hX]; rfl) isClosed_closure isIrreducible_singleton.closure
    hTcl hTirr hyT h2 hT2
  exact ⟨σ, rfl, rfl, heq.symm⟩

/-- The image of the closure of the generic point of a prime divisor `P` of a closed subscheme
`E` is the closure of its image. -/
private lemma image_support_eq_closure {X : Scheme.{0}} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme) :
    E.idealSheaf.subschemeι.base '' (P.support : Set E.idealSheaf.subscheme) =
      closure {E.idealSheaf.subschemeι P.genericPoint} := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← E.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq, Set.image_singleton]

/-- The divisor on `E` of a sum of edge systems along double surfaces `σ i` with first component
`E` carrying prime divisors `P i` of `E`. -/
private lemma surfaceCoefficientDivisor_sum_edgeSystem' {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {B : Divisor Z} {E : MMP.Mori.PrimeDivisor Z} {ι : Type*} [Fintype ι]
    (σ : ι → DoubleSurface B) (P : ι → MMP.Mori.PrimeDivisor E.idealSheaf.subscheme) (t : ι → ℚ)
    (h1 : ∀ i, (σ i).fst = E)
    (h3 : ∀ i, (σ i).carrier = closure {E.idealSheaf.subschemeι (P i).genericPoint}) :
    surfaceCoefficientDivisor (∑ i, edgeSystem (σ i) (t i)) E =
      ∑ i, Finsupp.single (P i) (t i) := by
  have : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  change surfaceCoefficientDivisorLinearMap B E _ = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    ConductorBlowup.surfaceCoefficientDivisor_edgeSystem_of_eq _ _ (h1 i) (P i) (h3 i)

/-- A dimension adding to `4` with a codimension at least `2` is at most `2`. -/
private lemma withBot_le_two_of_add {d : WithBot ℕ∞} {c : ℕ∞}
    (h : d + (c : WithBot ℕ∞) = 4) (hc : 2 ≤ c) : d ≤ 2 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + c = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
    suffices d ≤ 2 from WithBot.coe_le_coe.2 this
    induction d using ENat.recTopCoe <;> induction c using ENat.recTopCoe <;> simp at h' ⊢
    norm_cast at *
    omega

/-- An embedding preserves the Krull dimension of subsets. -/
private lemma topologicalKrullDim_image_of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) (T : Set X) :
    topologicalKrullDim (f '' T) = topologicalKrullDim T := by
  have hr : Set.range (f ∘ (Subtype.val : T → X)) = f '' T := by
    rw [Set.range_comp, Subtype.range_coe]
  exact ((hf.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr hr)).isHomeomorph.topologicalKrullDim_eq.symm

/-- The divisor on `E` of a sum of edge systems along double surfaces carrying the components of
a `ℚ`-divisor `c` of `E` is `c`. -/
private lemma surfaceCoefficientDivisor_sum_edgeSystem {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {B : Divisor Z} {E : MMP.Mori.PrimeDivisor Z}
    (c : QDivisor E.idealSheaf.subscheme) (σ : ∀ P ∈ c.support, DoubleSurface B)
    (h1 : ∀ P hP, (σ P hP).fst = E)
    (h3 : ∀ P hP, (σ P hP).carrier = closure {E.idealSheaf.subschemeι P.genericPoint}) :
    surfaceCoefficientDivisor (∑ P ∈ c.support.attach, edgeSystem (σ P.1 P.2) (c P.1)) E = c := by
  have : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  have hlin := map_sum (surfaceCoefficientDivisorLinearMap B E)
    (fun P : c.support => edgeSystem (σ P.1 P.2) (c P.1)) c.support.attach
  change surfaceCoefficientDivisorLinearMap B E _ = c
  rw [hlin]
  have hterm : ∀ P : c.support, surfaceCoefficientDivisorLinearMap B E
      (edgeSystem (σ P.1 P.2) (c P.1)) = Finsupp.single P.1 (c P.1) := fun P =>
    ConductorBlowup.surfaceCoefficientDivisor_edgeSystem_of_eq _ _ (h1 P.1 P.2) P.1 (h3 P.1 P.2)
  rw [Finset.sum_congr rfl fun P _ => hterm P,
    Finset.sum_attach c.support (fun P => Finsupp.single P (c P))]
  exact Finsupp.sum_single c

section Principal

/-- The stalk of `f⁻¹I · 𝒪_Y` at `y` is generated by the image of the stalk of `I` at `f y`. -/
private lemma stalk_comap' {X Y : Scheme.{0}} (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y) :
    IdealSheafData.stalk (I.comap f) y =
      (IdealSheafData.stalk I (f y)).map (f.stalkMap y).hom := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := ⊤) (by simp)
  obtain ⟨V, hV, hyV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := f ⁻¹ᵁ U) hyU
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨V, hV⟩ hyV,
    IdealSheafData.stalk_eq_map_germ _ (f y) ⟨U, hU⟩ hyU,
    Stacks.IdealSheaf.ideal_comap_appLE I f ⟨U, hU⟩ ⟨V, hV⟩ hVU, Ideal.map_map, Ideal.map_map]
  congr 1
  ext t
  simp only [RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
    CommRingCat.comp_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The local rings at the points of the smooth locus over a field are regular. -/
private lemma isRegularLocalRing_stalk_of_mem_smoothLocus' {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) {y : Y} (hy : y ∈ MMP.Mori.smoothLocus sY) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨V, hyV, hV⟩ := MMP.Mori.mem_smoothLocus_iff.1 hy
  haveI : Smooth (V.ι ≫ sY) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sY) ⟨y, hyV⟩
  exact IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨y, hyV⟩).commRingCatIsoToRingEquiv

/-- **Invertibility of the inverse image of a surface forces exceptionality.** If `r⁻¹ I_V` has
principal stalk at a point `y` over the generic point of a surface `V` along which `Y` is smooth
of codimension two, then `r` is not an isomorphism near `y`. -/
private lemma mem_exceptionalSet_of_isPrincipal {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (r : Z ⟶ Y) (V : IrreducibleCloseds Y) (v : Y) (hv : IsGenericPoint v (V : Set Y))
    (hsm : v ∈ MMP.Mori.smoothLocus sY)
    (hcoh : Order.coheight v = 2) (y : Z)
    (hy : r.base y = v)
    (hprinc : (AlgebraicGeometry.IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
      ⟨(V : Set Y), V.isClosed⟩).comap r) y).IsPrincipal) :
    y ∈ exceptionalSet r := by
  by_contra hne
  have hV : r.base y ∈ biregularLocus r := not_not.1 hne
  haveI : IsIso (r ∣_ biregularLocus r) := isBiregular_biregularLocus r
  haveI : IsIso (r.stalkMap y) :=
    isIso_stalkMap_of_isIso_morphismRestrict r (U := biregularLocus r) inferInstance hV
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨(V : Set Y), V.isClosed⟩ : Closeds Y)
  haveI : IsReduced D.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  haveI : IrreducibleSpace D.subscheme :=
    MMP.Intersection.Scheme.IdealSheafData.irreducibleSpace_subscheme_vanishingIdeal V.isIrreducible
  haveI : IsIntegral D.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hDgen : D.subschemeι (genericPoint D.subscheme) = r.base y := by
    rw [hy]
    refine IsGenericPoint.eq ?_ hv
    change closure _ = _
    rw [← Set.image_singleton, D.subschemeι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec D.subscheme).def, Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [stalk_comap'] at hprinc
  -- transport the principal stalk back along the isomorphism of local rings
  set e := (asIso (r.stalkMap y)).commRingCatIsoToRingEquiv
  have hprinc' : (IdealSheafData.stalk D (r.base y)).IsPrincipal := by
    obtain ⟨g, hg⟩ := hprinc
    refine ⟨e.symm g, ?_⟩
    have h1 : IdealSheafData.stalk D (r.base y) =
        ((IdealSheafData.stalk D (r.base y)).map (r.stalkMap y).hom).map
          (e.symm : _ →+* _) := by
      rw [Ideal.map_map]
      have : (e.symm : _ →+* _).comp (r.stalkMap y).hom = RingHom.id _ := by
        ext t
        exact e.symm_apply_apply t
      rw [this, Ideal.map_id]
    rw [h1, hg]
    change Ideal.map (e.symm : _ →+* _) (Ideal.span {g}) = Ideal.span {e.symm g}
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hmax := IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal D
  rw [hDgen] at hmax
  rw [hmax] at hprinc'
  haveI := isRegularLocalRing_stalk_of_mem_smoothLocus' sY (hy ▸ hsm)
  have hdim := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Y.presheaf.stalk (r.base y))
  have hc : Order.coheight (r.base y) = 2 := by rw [hy]; exact hcoh
  rw [ringKrullDim_stalk_eq_coheight, hc] at hdim
  obtain ⟨g, hg⟩ := hprinc'
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := Y.presheaf.stalk (r.base y))
    (Set.finite_singleton g)
  rw [← hg, Set.ncard_singleton] at hle
  have : ((Submodule.spanFinrank (IsLocalRing.maximalIdeal (Y.presheaf.stalk (r.base y))) : ℕ) :
      WithBot ℕ∞) ≤ 1 := by exact_mod_cast hle
  rw [hdim] at this
  exact absurd this (by decide)

end Principal

/-- On an snc resolution model, the image in `Z` of the generic point of a prime divisor `P` of a
prime divisor `G` of `Z` is the generic point of a surface. -/
private lemma topologicalKrullDim_closure_subschemeι_genericPoint {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Z.Over (Spec (.of ℂ))]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} (hMr : ConductorBlowup.IsSNCResolutionModel sY r)
    (G : MMP.Mori.PrimeDivisor Z) (P : MMP.Mori.PrimeDivisor G.idealSheaf.subscheme) :
    topologicalKrullDim (closure ({G.idealSheaf.subschemeι P.genericPoint} : Set Z)) =
      ((2 : ℕ) : WithBot ℕ∞) := by
  rw [← image_support_eq_closure, topologicalKrullDim_image_of_isEmbedding
    G.idealSheaf.subschemeι.isClosedEmbedding.isEmbedding,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ConductorBlowup.topologicalKrullDim_closure_genericPoint_eq_two sY r hMr G P

/-- **Exceptional surfaces of a strict component are double surfaces.** Let `G` be a
non-exceptional component of an snc boundary `B ⊇ F`, where `F` is the reduced exceptional divisor
of `r`. A surface of `G` whose generic point is exceptional for `r` is a double surface of `B`
between `G` and a component of `F`. -/
private lemma exists_doubleSurface_of_mem_exceptionalSet {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y}
    (hMr : ConductorBlowup.IsSNCResolutionModel sY r) {B F : Divisor Z}
    (hBsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) B) (hFB : F.support ⊆ B.support)
    (hFsupp : (F.supp : Set Z) = exceptionalSet r) {G : MMP.Mori.PrimeDivisor Z}
    (hG : G ∈ B.support) (hGF : G ∉ F.support) (P : MMP.Mori.PrimeDivisor G.idealSheaf.subscheme)
    (hy : G.idealSheaf.subschemeι P.genericPoint ∈ exceptionalSet r) :
    ∃ σ : DoubleSurface B, σ.fst = G ∧ σ.snd ∈ F.support ∧
      σ.carrier = closure {G.idealSheaf.subschemeι P.genericPoint} := by
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  haveI : IsLocallyNoetherian Z := hMr.isLocallyNoetherian
  haveI : IsIntegral Z := hMr.isResolution.2.1.toIsIntegral
  have hyF : G.idealSheaf.subschemeι P.genericPoint ∈ (F.supp : Set Z) := hFsupp ▸ hy
  rw [ConductorBlowup.coe_supp_eq_iUnion] at hyF
  obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.1 hyF
  have hyG : G.idealSheaf.subschemeι P.genericPoint ∈ (G.support : Set Z) := by
    have : G.idealSheaf.subschemeι P.genericPoint ∈ Set.range G.idealSheaf.subschemeι := ⟨_, rfl⟩
    rwa [G.idealSheaf.range_subschemeι] at this
  obtain ⟨σ, h1, h2, h3⟩ := exists_doubleSurface_of_mem_of_isSNC hMr.topologicalKrullDim_eq hBsnc
    hG (hFB hE) (fun h => hGF (h ▸ hE)) hyG hyE
    (by rw [topologicalKrullDim_closure_subschemeι_genericPoint hMr]; rfl)
  exact ⟨σ, h1, h2 ▸ hE, h3⟩

/-- **The key inequality.** On a simultaneous conductor model `r : Z ⟶ Y` of the reduced union
`Q`, the branch excess over the surfaces `V ∈ 𝒱` with several branches is bounded by the divisor
cycle ranks of the normalized components and the dimension of `D_{v,Q}(r)`. -/
private lemma sum_boundaryBranchCount_sub_one_le_finrank_verticalDefectOver {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 4)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : MMP.Mori.IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 4)
    (hYQ : IsQFactorial sY)
    (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (hpQ : topologicalKrullDim (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) ≤ 1)
    (𝒱fin : Finset (IrreducibleCloseds Y))
    (h𝒱 : ∀ V, V ∈ 𝒱fin ↔ topologicalKrullDim (V : Set Y) = 2 ∧
      (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q V)
    (Qd : Divisor Y) (hQd : MMP.Intersection.IsReducedEffective Qd)
    (hQdsupp : (Qd.supp : Set Y) = ⋃ S ∈ Q, (S.support : Set Y))
    (hsm : ∀ y : Y, y ∉ smoothLocus sY → topologicalKrullDim (closure ({y} : Set Y)) ≤ 1)
    {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (r : Z ⟶ Y)
    (hcompr : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hres : MMP.Intersection.IsResolution sY r)
    (hsnc1 : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ))
      (r.base ⁻¹' (Qd.supp : Set Y) ∪ exceptionalSet r))
    (hsnc2 : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) (exceptionalSet (r ≫ p)))
    (hD : ∃ D : Divisor Z, (∀ P, 0 ≤ D.coeff P) ∧
      (D.supp : Set Z) = exceptionalSet (r ≫ p) ∧
      ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (r ≫ p) h)
    (hprinc : ∀ V ∈ 𝒱fin, ∀ z : Z,
      (AlgebraicGeometry.IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(V : Set Y), V.isClosed⟩).comap r) z).IsPrincipal)
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFsnc : DivisorWithCoeffs.IsSNC (r ≫ sY) F)
    (hFsupp : (F.supp : Set Z) = exceptionalSet r) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYproj.toIsVariety.toLocallyOfFiniteType
    haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcompr⟩
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hres.2.2.2.1
    ∑ V ∈ 𝒱fin, ((boundaryBranchCount Q V : ℤ) - 1) ≤
      ((∑ S ∈ Q,
          letI := primeDivisorNormalizationOver sY S
          haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
        (Module.finrank ℚ (verticalDefectOver r F (Qd.supp : Set Y)) : ℤ) := by
  classical
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYproj.toIsVariety.toLocallyOfFiniteType
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcompr⟩
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hres.2.2.2.1
  haveI : IsComplexScheme Y := isComplexScheme_of_isProjectiveVariety Y hYproj
  have hrc : IsClosedMap r.base := r.isClosedMap
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  have hZproj : IsProjective (Z ↘ Spec (.of ℂ)) := by
    rw [← hcompr]
    exact (IsProjectiveMorphism.isProjective hres.2.2.2.1).comp
      (IsProjectiveMorphism.isProjective hYproj.isProjective)
  haveI hYv : AlgebraicGeometry.IsVariety ℂ sY := hYproj.toIsVariety
  haveI hZv : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hres.2.1
  have hZdim : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2, hYdim]
  have hMr : ConductorBlowup.IsSNCResolutionModel sY r :=
    ⟨‹_›, ‹_›, ‹_›, ‹_›, hcompr, hres, hZproj, hZdim, ⟨F, hFred, hFsnc, hFsupp⟩⟩
  -- the boundary `B` with support `r⁻¹(Q) ∪ Ex(r)` and the antiample divisor `D`
  obtain ⟨B, hBred, hBsnc, hBsupp⟩ : ∃ B : Divisor Z, MMP.Intersection.IsReducedEffective B ∧
      DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) B ∧
      (B.supp : Set Z) = r.base ⁻¹' (Qd.supp : Set Y) ∪ exceptionalSet r :=
    exists_reducedDivisor_of_subset (hcompr ▸ hres.2.2.1) hsnc1 hsnc1.1
      (isPureCodimOne_of_isSNCClosedSubset hsnc1) le_rfl
  obtain ⟨D, hD0, hDsupp, hDcart, hDamp⟩ := hD
  have hDsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) D := by
    obtain ⟨D', -, hD'snc, hD'supp⟩ := exists_reducedDivisor_of_subset (hcompr ▸ hres.2.2.1)
      hsnc2 hsnc2.1 (isPureCodimOne_of_isSNCClosedSubset hsnc2) le_rfl
    refine hD'snc.of_support_subset fun P hP => mem_support_of_support_subset_supp ?_
    rw [hD'supp, ← hDsupp]
    exact support_subset_supp_of_mem hP
  have hDpos : ∀ P ∈ D.support, 0 < D.coeff P := fun P hP =>
    lt_of_le_of_ne (hD0 P) (Ne.symm (Finsupp.mem_support_iff.1 hP))
  have hFB : F.support ⊆ B.support := fun E hE =>
    mem_support_of_support_subset_supp ((support_subset_supp_of_mem hE).trans
      (by rw [hFsupp, hBsupp]; exact Set.subset_union_right))
  have hexc : r.base ⁻¹' (Qd.supp : Set Y) ∪ exceptionalSet r ⊆ exceptionalSet (r ≫ p) := by
    haveI : IsIntegral Z := hZv.toIsIntegral
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hpproj
    have hrsurj := surjective_of_isBirationalMorphism r hrc hres.2.2.2.2
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYv.toLocallyOfFiniteType
    have hQex : (Qd.supp : Set Y) ⊆ exceptionalSet p := by
      rw [hQdsupp]
      intro y hy
      obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 hy
      refine ConductorBlowup.subset_exceptionalSet_of_lt p
        ⟨(S.support : Set Y), MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support S,
          MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support S⟩ (n := 3)
        (ConductorBlowup.topologicalKrullDim_support_eq_three hYdim S) ?_ hyS
      refine lt_of_le_of_lt ((topologicalKrullDim_mono' (Set.image_mono
        (Set.subset_biUnion_of_mem (u := fun S : MMP.Mori.PrimeDivisor Y => (S.support : Set Y))
          hS))).trans hpQ) ?_
      exact_mod_cast (by decide : (1 : ℕ∞) < 3)
    rintro z (hz | hz)
    · exact ConductorBlowup.preimage_exceptionalSet_subset r hrsurj p (hQex hz)
    · exact ConductorBlowup.exceptionalSet_subset_comp r hrsurj p hz
  have hBD : B.support ⊆ D.support := fun G hG =>
    mem_support_of_support_subset_supp ((support_subset_supp_of_mem hG).trans
      (by rw [hBsupp, hDsupp]; exact hexc))
  have hFex : ∀ E ∈ F.support, E.genericPoint ∈ exceptionalSet r := fun E hE => by
    have := support_subset_supp_of_mem hE (genericPoint_mem_support' E)
    rwa [hFsupp] at this
  haveI : FiniteDimensional ℚ (ComponentHomology F) :=
    (finiteDimensional_componentHomology_and_verticalDefect hcompr hYproj hYQ hres hZdim hFred
      hFsnc hFsupp).1
  have hcoh : ∀ G ∈ B.support, ∀ x : G.idealSheaf.subscheme,
      topologicalKrullDim (closure ({x} : Set G.idealSheaf.subscheme)) =
        ((2 : ℕ) : WithBot ℕ∞) → Order.coheight x = 1 := fun G _ x hx =>
    ConductorBlowup.coheight_eq_one_of_isSNCResolutionModel sY r hMr G x hx
  haveI hXv : AlgebraicGeometry.IsVariety ℂ sX := hXproj.toIsVariety
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have hpdim : ∀ T : Set Y, IsClosed T → topologicalKrullDim T ≤ 1 →
      topologicalKrullDim (p.base '' T) ≤ 1 := fun T hT hT1 =>
    Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ sY sX p hp T hT 1
      (by exact_mod_cast hT1) _ (p.isClosedMap _ hT) le_rfl
  have hV2 : ∀ v w : Y, topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞) →
      topologicalKrullDim (closure ({w} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞) →
      closure ({w} : Set Y) ⊆ closure {v} → w = v := by
    intro v w hv hw hwv
    exact eq_of_closure_eq (ConductorBlowup.eq_of_subset_of_topologicalKrullDim_eq
      (d := 4) (by rw [hYdim]; rfl) isClosed_closure isIrreducible_singleton.closure
      isClosed_closure isIrreducible_singleton.closure hwv hw hv)
  have hf : MMP.Intersection.IsResolution sX (r ≫ p) := by
    have hrp : (r ≫ p) ≫ sX = r ≫ sY := by rw [Category.assoc, hp]
    refine ⟨hXv, ?_, ?_, hres.2.2.2.1.comp hpproj, ?_⟩
    · rw [hrp]; exact hres.2.1
    · rw [hrp]; exact hres.2.2.1
    · haveI : IsIntegral Z := hZv.toIsIntegral
      exact isBirationalMorphism_comp' hres.2.2.2.2 hpbir
  have hcompX : (r ≫ p) ≫ sX = Z ↘ Spec (.of ℂ) := by
    rw [Category.assoc, hp, hcompr]
  have hpQ' : topologicalKrullDim (p.base '' (Qd.supp : Set Y)) ≤ 1 := hQdsupp ▸ hpQ
  -- the conductor surfaces as subvarieties
  let toS : 𝒱fin → Y := fun V => V.1.isIrreducible.genericPoint
  have htoS : ∀ V, closure ({toS V} : Set Y) = V.1 := fun V =>
    V.1.isIrreducible.isGenericPoint_genericPoint V.1.isClosed
  have htoS_inj : Function.Injective toS := fun V V' h => by
    apply Subtype.ext
    apply SetLike.coe_injective
    rw [← htoS V, ← htoS V', h]
  let 𝒱 : Finset Y := Finset.univ.image toS
  have h𝒱card : 𝒱.card = 𝒱fin.card := by
    rw [Finset.card_image_of_injective _ htoS_inj, Finset.card_univ, Fintype.card_coe]
  have h𝒱dim : ∀ v ∈ 𝒱, topologicalKrullDim (closure ({v} : Set Y)) = ((2 : ℕ) : WithBot ℕ∞) := by
    intro v hv
    obtain ⟨V', -, rfl⟩ := Finset.mem_image.1 hv
    rw [htoS, ((h𝒱 V'.1).1 V'.2).1]
    rfl
  have hVQ : ∀ v ∈ 𝒱, closure ({v} : Set Y) ⊆ (Qd.supp : Set Y) := by
    intro v hv
    obtain ⟨V', -, rfl⟩ := Finset.mem_image.1 hv
    rw [htoS, hQdsupp]
    exact ((h𝒱 V'.1).1 V'.2).2.1
  -- the strict components of `Q`
  obtain ⟨st, hst_inj, hst_B, hst_F, hst_ex, hst_cov, hst_gen, hst_iso⟩ :
      ∃ st : Q → MMP.Mori.PrimeDivisor Z, Function.Injective st ∧ (∀ S, st S ∈ B.support) ∧
        (∀ S, st S ∉ F.support) ∧ (∀ S, (st S).genericPoint ∉ exceptionalSet r) ∧
        (∀ G ∈ B.support, G ∉ F.support → ∃ S, st S = G) ∧
        (∀ S, r.base (st S).genericPoint = (S : MMP.Mori.PrimeDivisor Y).genericPoint) ∧
        ∀ S, IsIso (r.stalkMap (st S).genericPoint) :=
    exists_strictComponents sY hYv r hZv hres.2.2.2.2 Q _ hQdsupp B F hBsupp hFsupp
  have hst_img : ∀ S, r.base '' (st S).support ⊆ ((S : MMP.Mori.PrimeDivisor Y).support : Set Y) :=
    fun S => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine (image_closure_subset_closure_image r.base.hom.continuous).trans ?_
      rw [Set.image_singleton, hst_gen]
  have hst_Q : ∀ S, r.base '' (st S).support ⊆ (Qd.supp : Set Y) := fun S => by
    refine (hst_img S).trans ?_
    rw [hQdsupp]
    exact Set.subset_biUnion_of_mem (u := fun S : MMP.Mori.PrimeDivisor Y => (S.support : Set Y))
      S.2
  have hst_V : ∀ S, ∀ v ∈ 𝒱, r.base '' (st S).support ≠ closure ({v} : Set Y) := by
    intro S v hv h
    have hη : (S : MMP.Mori.PrimeDivisor Y).genericPoint ∈ closure ({v} : Set Y) := by
      rw [← h, ← hst_gen S]
      exact ⟨_, genericPoint_mem_support' _, rfl⟩
    have hsub : ((S : MMP.Mori.PrimeDivisor Y).support : Set Y) ⊆ closure ({v} : Set Y) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_minimal (Set.singleton_subset_iff.2 hη) isClosed_closure
    have h3 := ConductorBlowup.topologicalKrullDim_support_eq_three hYdim S.1
    have := topologicalKrullDim_mono' hsub
    rw [h3, h𝒱dim v hv] at this
    exact absurd this (by decide)
  -- the normalized components and the strict transforms
  letI instN : ∀ S : Q, (primeDivisorNormalizationScheme S.1).Over (Spec (.of ℂ)) :=
    fun S => primeDivisorNormalizationOver sY S.1
  haveI instNc : ∀ S : Q, IsComplexScheme (primeDivisorNormalizationScheme S.1) :=
    fun S => isComplexScheme_primeDivisorNormalizationScheme sY hYproj S.1
  haveI instNn : ∀ S : Q, IsNormal (primeDivisorNormalizationScheme S.1) := fun S =>
    haveI := S.1.integral
    Scheme.isNormal_normalizationScheme S.1.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hN : ∀ S : Q, MMP.Mori.IsProjectiveVariety ℂ
      (primeDivisorNormalizationScheme S.1 ↘ Spec (.of ℂ)) := fun S =>
    isProjectiveVariety_primeDivisorNormalization' S.1 sY hYproj
  have hZprojv : AlgebraicGeometry.IsProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    { toIsVariety := hcompr ▸ hZv, isProjective := hcompr ▸ hres.2.2.2.1.comp hYproj.isProjective }
  have hM : ∀ S : Q, MMP.Mori.IsProjectiveVariety ℂ
      ((st S).idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun S =>
    haveI : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hZprojv.toIsVariety
    { toIsVariety := isVariety_subschemeι' (st S) (Z ↘ Spec (.of ℂ)),
      isProjective := (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
        hZprojv.isProjective }
  have hMs : ∀ S : Q, MMP.Mori.IsSmoothScheme ((st S).idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    fun S => hBsnc.1 (st S) (hst_B S)
  have hMdim : ∀ S : Q, topologicalKrullDim (st S).idealSheaf.subscheme = 3 := fun S => by
    letI : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hZprojv.toIsVariety
    haveI : IsIntegral Z := hZv.toIsIntegral
    have h3 := ConductorBlowup.topologicalKrullDim_support_eq_three hZdim (st S)
    have hr : Set.range (st S).idealSheaf.subschemeι = ((st S).support : Set Z) :=
      (st S).idealSheaf.range_subschemeι
    rw [(((st S).idealSheaf.subschemeι.isClosedEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hr)).isHomeomorph.topologicalKrullDim_eq), h3]
    rfl
  have hstN : ∀ S : Q, IsNormal (st S).idealSheaf.subscheme := fun S =>
    ConductorBlowup.isNormal_subscheme_of_isSNC (Z ↘ Spec (.of ℂ)) hBsnc (hst_B S)
  obtain ⟨h, hh_comm, hh_over, hh_proj, hh_bir⟩ : ∃ h : ∀ S : Q,
      (st S).idealSheaf.subscheme ⟶ primeDivisorNormalizationScheme S.1,
      (∀ S, h S ≫ primeDivisorNormalization S.1 = (st S).idealSheaf.subschemeι ≫ r) ∧
      (∀ S, (h S).IsOver (Spec (.of ℂ))) ∧ (∀ S, IsProjectiveMorphism (h S)) ∧
      ∀ S, MMP.Mori.IsBirationalMorphism (h S) := by
    have := fun S : Q =>
      haveI := hstN S
      exists_lift_primeDivisorNormalization_of_strict sY S.1 (st S) r (hst_img S) (hst_gen S)
        (hst_iso S) (by rw [hcompr]; rfl) (hM S)
        (haveI := hYv; isVariety_primeDivisorNormalization' S.1 sY)
    choose h hh using this
    exact ⟨h, fun S => (hh S).1, fun S => (hh S).2.1, fun S => (hh S).2.2.1,
      fun S => (hh S).2.2.2⟩
  haveI := hh_over
  -- the branches over the conductor surfaces
  let Br : Q → Type := fun S => {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1) //
    ∃ V ∈ 𝒱fin, primeDivisorNormalization S.1 '' P.support = (V : Set Y)}
  have hBrV : ∀ S : Q, ∀ V ∈ 𝒱fin, {P : MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme S.1) |
      primeDivisorNormalization S.1 '' P.support = (V : Set Y)}.Finite := fun S V hV =>
    finite_branches_of_one_lt Q ((h𝒱 V).1 hV).2.2 S.1 S.2
  -- a branch determines its surface
  let eBr : ∀ S : Q, Br S ≃ Σ V : 𝒱fin, {P : MMP.Mori.PrimeDivisor
      (primeDivisorNormalizationScheme S.1) //
        primeDivisorNormalization S.1 '' P.support = ((V : IrreducibleCloseds Y) : Set Y)} :=
    fun S =>
    { toFun := fun b => ⟨⟨_, b.2.choose_spec.1⟩, b.1, b.2.choose_spec.2⟩
      invFun := fun P => ⟨P.2.1, P.1.1, P.1.2, P.2.2⟩
      left_inv := fun b => rfl
      right_inv := fun P => by
        obtain ⟨⟨V, hV⟩, P, hP⟩ := P
        have hex : ∃ V' ∈ 𝒱fin, primeDivisorNormalization S.1 '' P.support = (V' : Set Y) :=
          ⟨V, hV, hP⟩
        have hV' : hex.choose = V := by
          apply SetLike.coe_injective
          exact hex.choose_spec.2.symm.trans hP
        exact Sigma.subtype_ext (Subtype.ext hV') rfl }
  haveI : ∀ S, Finite (Br S) := fun S => by
    haveI : ∀ V : 𝒱fin, Finite {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1) //
        primeDivisorNormalization S.1 '' P.support = ((V : IrreducibleCloseds Y) : Set Y)} :=
      fun V => (hBrV S V.1 V.2).to_subtype
    exact Finite.of_equiv _ (eBr S).symm
  letI : ∀ S, Fintype (Br S) := fun S => Fintype.ofFinite _
  have hVb : ∀ S (b : Br S), ∃ V : 𝒱fin,
      primeDivisorNormalization S.1 '' b.1.support = (V : Set Y) := fun S b => by
    obtain ⟨V, hV, h⟩ := b.2
    exact ⟨⟨V, hV⟩, h⟩
  choose Vb0 hVb0 using hVb
  let Vb : ∀ S, Br S → 𝒱 := fun S b => ⟨toS (Vb0 S b), Finset.mem_image_of_mem _ (by simp)⟩
  -- the branch legs
  obtain ⟨leg, hleg_fst, hleg_snd, hleg_inj, hleg_img, hleg_sndimg, hleg_div⟩ :
      ∃ leg : ∀ S, Br S → DoubleSurface B, (∀ S b, (leg S b).fst = st S) ∧
        (∀ S b, (leg S b).snd ∈ F.support) ∧ (∀ S, Function.Injective (leg S)) ∧
        (∀ S b, r.base '' (leg S b).carrier = closure ({(Vb S b).1} : Set Y)) ∧
        (∀ S b, r.base '' (leg S b).snd.support = closure ({(Vb S b).1} : Set Y)) ∧
        ∀ S (u : Br S → ℚ),
          surfaceCoefficientDivisor (∑ b, edgeSystem (leg S b) (u b)) (st S) =
            inverseTransformDivisor (h S) (∑ b, Finsupp.single (b : Br S).1 (u b)) := by
    haveI : IsIntegral Z := hZv.toIsIntegral
    haveI : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hZprojv.toIsVariety
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYv.toLocallyOfFiniteType
    haveI : ∀ S : Q, IsProper (h S) := fun S => isProper_of_isProjectiveMorphism _ (hh_proj S)
    have hcodr := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sY r
      (hY := hYv) (hX := hZv)
      hres.2.2.2.2
    -- the generic point of a conductor surface
    have hgenV : ∀ V : 𝒱fin, Order.coheight (toS V) = 2 ∧
        toS V ∈ MMP.Mori.smoothLocus sY := by
      intro V
      have hd : topologicalKrullDim (closure ({toS V} : Set Y)) = 2 := by
        rw [htoS]; exact ((h𝒱 V.1).1 V.2).1
      refine ⟨?_, ?_⟩
      · have h4 := ConductorBlowup.topologicalKrullDim_closure_add_coheight (X := Y)
          (toS V)
        rw [hd, hYdim] at h4
        revert h4
        generalize Order.coheight (toS V) = c
        intro h4
        have h5 : ((2 + c : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
          rw [WithBot.coe_add]; exact h4
        have h6 : 2 + c = 4 := WithBot.coe_injective h5
        induction c using ENat.recTopCoe with
        | top => simp at h6
        | coe c =>
          have : 2 + c = 4 := by exact_mod_cast h6
          have hc : c = 2 := by omega
          rw [hc]; rfl
      · by_contra hns
        have := hsm _ hns
        rw [hd] at this
        exact absurd this (by decide)
    have hleg1 : ∀ S (b : Br S), ∃ (Pt : MMP.Mori.PrimeDivisor (st S).idealSheaf.subscheme)
        (σ : DoubleSurface B),
        inverseTransformPrimeDivisor (h S) b.1 = some Pt ∧ σ.fst = st S ∧ σ.snd ∈ F.support ∧
        σ.carrier = closure {(st S).idealSheaf.subschemeι Pt.genericPoint} ∧
        r.base '' σ.carrier = ((Vb0 S b : IrreducibleCloseds Y) : Set Y) ∧
        r.base '' σ.snd.support = ((Vb0 S b : IrreducibleCloseds Y) : Set Y) ∧
        (h S).base Pt.genericPoint = b.1.genericPoint := by
      intro S b
      set V := Vb0 S b
      -- the strict transform of the branch
      have hηP : b.1.genericPoint ∈ biregularLocus (h S) := by
        have hNv : AlgebraicGeometry.IsVariety ℂ (primeDivisorNormalizationScheme S.1 ↘
            Spec (.of ℂ)) := (hN S).toIsVariety
        have hMv : AlgebraicGeometry.IsVariety ℂ (h S ≫ (primeDivisorNormalizationScheme S.1 ↘
            Spec (.of ℂ))) := by
          rw [(hh_over S).comp_over]; exact (hM S).toIsVariety
        have hcod := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus _ (h S)
          (hY := hNv) (hX := hMv)
          (hh_bir S)
        by_contra hη
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcod _ hη
        rw [b.1.coheight_genericPoint] at this
        exact absurd this (by decide)
      obtain ⟨Pt, hPt, hPtgen⟩ :=
        MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := h S) b.1 hηP
      set y := (st S).idealSheaf.subschemeι Pt.genericPoint with hy
      -- `y` lies over the generic point of `V`
      have hνgen : IsGenericPoint (primeDivisorNormalization S.1 b.1.genericPoint) (V : Set Y) := by
        have h1 := (AlgebraicGeometry.PrimeDivisor.support_eq_closure b.1 ▸
          isGenericPoint_closure (x := b.1.genericPoint)).image
          (primeDivisorNormalization S.1).base.hom.continuous
        haveI : IsFinite (primeDivisorNormalization S.1) := by
          haveI := hYv; exact isFinite_primeDivisorNormalization' S.1 sY
        rwa [((primeDivisorNormalization S.1).isClosedMap _
          (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support b.1)).closure_eq,
          hVb0 S b] at h1
      have hry : r.base y = toS V := by
        have h1 : r.base y = primeDivisorNormalization S.1 b.1.genericPoint := by
          rw [hy, ← hPtgen, ← Scheme.Hom.comp_apply, ← hh_comm, Scheme.Hom.comp_apply]
        rw [h1]
        refine hνgen.eq ?_
        exact htoS V
      -- `y` is exceptional
      have hyex : y ∈ exceptionalSet r :=
        mem_exceptionalSet_of_isPrincipal sY r V.1 (toS V) (htoS V) (hgenV V).2 (hgenV V).1 y hry
          (hprinc V.1 V.2 y)
      obtain ⟨σ, hσ1, hE, hσ3⟩ := exists_doubleSurface_of_mem_exceptionalSet hMr hBsnc hFB
        hFsupp (hst_B S) (hst_F S) Pt hyex
      set E := σ.snd
      have hyE : y ∈ (E.support : Set Z) :=
        (σ.carrier_subset (hσ3 ▸ subset_closure rfl : y ∈ σ.carrier)).2
      -- the images
      have himgy : r.base '' closure {y} = (V : Set Y) := by
        rw [← hrc.closure_image_eq_of_continuous r.base.hom.continuous, Set.image_singleton, hry,
          htoS V]
      refine ⟨Pt, σ, hPt, hσ1, hE, hσ3, hσ3 ▸ himgy, ?_, hPtgen⟩
      -- `E` is exceptional, so maps to a set of dimension at most two containing `V`
      have hEimg : r.base '' (E.support : Set Z) = closure {r.base E.genericPoint} := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          ← hrc.closure_image_eq_of_continuous r.base.hom.continuous, Set.image_singleton]
      have hcohE : 2 ≤ Order.coheight (r.base E.genericPoint) :=
        MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcodr _ (hFex E hE)
      have hdE : topologicalKrullDim (closure ({r.base E.genericPoint} : Set Y)) ≤ 2 := by
        have h4 := ConductorBlowup.topologicalKrullDim_closure_add_coheight (X := Y)
          (r.base E.genericPoint)
        rw [hYdim] at h4
        exact withBot_le_two_of_add h4 hcohE
      have hVsub : (V : Set Y) ⊆ r.base '' (E.support : Set Z) := by
        rw [← himgy]
        exact Set.image_mono (closure_minimal (Set.singleton_subset_iff.2 hyE)
          (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support E))
      have hV2' : topologicalKrullDim (V : Set Y) = ((2 : ℕ) : WithBot ℕ∞) := by
        rw [← htoS V]; exact h𝒱dim _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      have hT2 : topologicalKrullDim (r.base '' (E.support : Set Z)) = ((2 : ℕ) : WithBot ℕ∞) := by
        refine le_antisymm (hEimg ▸ hdE) ?_
        rw [← hV2']
        exact topologicalKrullDim_mono' hVsub
      refine (ConductorBlowup.eq_of_subset_of_topologicalKrullDim_eq (d := 4) (by rw [hYdim]; rfl)
        V.1.isClosed V.1.isIrreducible (hEimg ▸ isClosed_closure)
        (hEimg ▸ isIrreducible_singleton.closure) hVsub hV2' hT2).symm
    choose Pt σ hPt hσ1 hσ2 hσ3 hσ4 hσ5 hσ6 using hleg1
    refine ⟨σ, hσ1, hσ2, fun S b b' hbb => ?_, fun S b => (hσ4 S b).trans (htoS _).symm,
      fun S b => (hσ5 S b).trans (htoS _).symm, fun S u => ?_⟩
    · have hc := congrArg DoubleSurface.carrier hbb
      rw [hσ3, hσ3] at hc
      have hins := (inseparable_iff_closure_eq.2 hc).eq
      have h1 := (st S).idealSheaf.subschemeι.isClosedEmbedding.injective hins
      have h2 : b.1.genericPoint = b'.1.genericPoint := by
        rw [← hσ6, ← hσ6, h1]
      exact Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h2)
    · rw [surfaceCoefficientDivisor_sum_edgeSystem' (σ S) (Pt S) u (hσ1 S) (hσ3 S), map_sum]
      exact Finset.sum_congr rfl fun b _ =>
        (inverseTransformDivisor_single_of_eq_some (hPt S b) (u b)).symm
  -- the strict-transform corrections as coefficient systems
  have hκ : ∀ S (c : QDivisor (st S).idealSheaf.subscheme),
      (∀ P ∈ c.support, topologicalKrullDim ((h S).base '' P.support) ≤ 1) →
      ∃ a ∈ orientedSurfaceCoefficients B,
        (∀ σ, a σ ≠ 0 → ((σ.fst = st S ∧ σ.snd ∈ F.support) ∨
            (σ.snd = st S ∧ σ.fst ∈ F.support)) ∧
          topologicalKrullDim (r.base '' σ.carrier) ≤ 1) ∧
        surfaceCoefficientDivisor a (st S) = c := by
    intro S c hc
    haveI : IsProper (h S) := isProper_of_isProjectiveMorphism _ (hh_proj S)
    haveI : IsIntegral Z := hZv.toIsIntegral
    haveI : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hZprojv.toIsVariety
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    have hdimN : ∀ T : Set (primeDivisorNormalizationScheme S.1), IsClosed T →
        topologicalKrullDim T ≤ 1 →
        topologicalKrullDim (primeDivisorNormalization S.1 '' T) ≤ 1 := by
      intro T hT hT1
      haveI := isVariety_primeDivisorNormalization' S.1 sY
      haveI : IsFinite (primeDivisorNormalization S.1) := isFinite_primeDivisorNormalization' S.1 sY
      exact Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ
        (primeDivisorNormalization S.1 ≫ sY) sY _ rfl T hT 1 (by exact_mod_cast hT1) _
        ((primeDivisorNormalization S.1).isClosedMap _ hT) le_rfl
    -- each component of `c` is a double surface of `(st S, E)` for an exceptional `E`
    have hP : ∀ P ∈ c.support, ∃ σ : DoubleSurface B, σ.fst = st S ∧ σ.snd ∈ F.support ∧
        σ.carrier = closure {(st S).idealSheaf.subschemeι P.genericPoint} ∧
        topologicalKrullDim (r.base '' σ.carrier) ≤ 1 := by
      intro P hPc
      set y := (st S).idealSheaf.subschemeι P.genericPoint
      have himg : r.base '' closure {y} =
          primeDivisorNormalization S.1 '' ((h S).base '' P.support) := by
        rw [← image_support_eq_closure, ← Set.image_comp, ← Set.image_comp]
        congr 1
        funext x
        change ((st S).idealSheaf.subschemeι ≫ r) x = (h S ≫ primeDivisorNormalization S.1) x
        rw [hh_comm]
      have hrdim : topologicalKrullDim (r.base '' closure {y}) ≤ 1 := by
        rw [himg]
        exact hdimN _ ((h S).isClosedMap _
          (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P))
          (hc P hPc)
      have hyex : y ∈ exceptionalSet r :=
        ConductorBlowup.subset_exceptionalSet_of_lt r
          ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ (n := 2)
          (topologicalKrullDim_closure_subschemeι_genericPoint hMr (st S) P)
          (lt_of_le_of_lt hrdim (by exact_mod_cast (by decide : (1 : ℕ∞) < 2)))
          (subset_closure rfl)
      obtain ⟨σ, h1, h2, h3⟩ := exists_doubleSurface_of_mem_exceptionalSet hMr hBsnc hFB hFsupp
        (hst_B S) (hst_F S) P hyex
      exact ⟨σ, h1, h2, h3, h3 ▸ hrdim⟩
    choose σP hσ1 hσ2 hσ3 hσ4 using hP
    let a : DoubleSurface B → ℚ := ∑ P ∈ c.support.attach,
      edgeSystem (σP P.1 P.2) (c P.1)
    refine ⟨a, Submodule.sum_mem _ fun P _ => edgeSystem_mem_orientedSurfaceCoefficients _ _,
      fun σ hσ => ?_, ?_⟩
    · simp only [a, Finset.sum_apply] at hσ
      obtain ⟨P, -, hPσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hσ
      by_cases h1 : σ = σP P.1 P.2
      · subst h1
        exact ⟨Or.inl ⟨hσ1 _ _, hσ2 _ _⟩, hσ4 _ _⟩
      · by_cases h2 : σ = (σP P.1 P.2).swap
        · subst h2
          refine ⟨Or.inr ⟨hσ1 _ _, hσ2 _ _⟩, ?_⟩
          rw [DoubleSurface.swap_carrier]
          exact hσ4 _ _
        · exact absurd (edgeSystem_apply_of_ne _ _ _ h1 h2) hPσ
    · exact surfaceCoefficientDivisor_sum_edgeSystem c σP hσ1 hσ3
  -- the generic balancing along the conductor surfaces
  have hvert : ∀ v ∈ 𝒱, ∀ a ∈ orientedSurfaceCoefficients B,
      (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = closure ({v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ = 0) →
      ∃ c ∈ orientedSurfaceCoefficients B,
        (∀ σ : DoubleSurface B, c σ ≠ a σ →
          r.base '' σ.fst.support = closure ({v} : Set Y) ∧
            r.base '' σ.snd.support = closure ({v} : Set Y)) ∧
        (∀ E ∈ B.support, r.base '' E.support = closure ({v} : Set Y) →
          Chow.rationalCoeff 𝔠 _ (2 : ℕ) v (componentPushforward r E 2
            (Chow.divisorCycle _ (surfaceCoefficientDivisor c E))) = 0) ∧
        ∀ σ : DoubleSurface B, c σ ≠ a σ → r.base '' σ.carrier ⊆ closure ({v} : Set Y) := by
    intro v hv a ha hsum
    have hVQ' : v ∈ Qd.supp := hVQ v hv (subset_closure rfl)
    have hv2 : δ[Y] v = 2 :=
      (ConductorBlowup.relativeDimension_eq_iff_topologicalKrullDim_closure _ v 2).2 (h𝒱dim v hv)
    have hBsnc' : DivisorWithCoeffs.IsSNC (r ≫ Y ↘ Spec (.of ℂ)) B := by
      have h : r ≫ Y ↘ Spec (.of ℂ) = Z ↘ Spec (.of ℂ) := hcompr
      rw [h]; exact hBsnc
    obtain ⟨c, hc, h1, h2, h3⟩ :=
      MMP.Fourfold.exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero_of_mem_supp
        hYdim Qd r hres B hBsnc' hBsupp v hv2 hVQ' a ha hsum
    exact ⟨c, hc, h1, h2, fun σ hσ => (h3 σ hσ).1⟩
  have hmain := card_le_of_branchLegs sX r p hrc hf hcompX hZproj hZdim B F D hDsnc hDpos
    ⟨hDcart, hDamp⟩ hFB hBD hFex hcoh (Qd.supp : Set Y) hpQ' hpdim hV2 st hst_inj hst_B hst_F
    hst_ex hst_cov hst_Q 𝒱 h𝒱dim hst_V hVQ
    (fun S : Q => primeDivisorNormalizationScheme S.1) hN h hM
    hMs
    hMdim hh_proj hh_bir Br (fun S b => b.1) Vb leg hleg_fst hleg_snd hleg_inj hleg_img
    hleg_sndimg hleg_div hκ hvert
  -- counting the branches and bounding the divisor classes
  have hcount : ∑ S : Q, Fintype.card (Br S) = ∑ V ∈ 𝒱fin, boundaryBranchCount Q V := by
    have h1 : ∀ S : Q, Fintype.card (Br S) = ∑ V ∈ 𝒱fin, branchNumber S.1 (V : Set Y) := by
      intro S
      haveI : ∀ V : 𝒱fin, Finite {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1) //
          primeDivisorNormalization S.1 '' P.support = ((V : IrreducibleCloseds Y) : Set Y)} :=
        fun V => (hBrV S V.1 V.2).to_subtype
      rw [Fintype.card_eq_nat_card, Nat.card_congr (eBr S), Nat.card_sigma,
        ← Finset.sum_coe_sort 𝒱fin]
      refine Finset.sum_congr rfl fun V _ => ?_
      rw [branchNumber, ← Nat.card_coe_set_eq]
      rfl
    have h2 : ∀ V ∈ 𝒱fin, boundaryBranchCount Q V = ∑ S ∈ Q, branchNumber S (V : Set Y) :=
      fun V hV => boundaryBranchCount_eq_sum fun S hS =>
        finite_branches_of_one_lt Q ((h𝒱 V).1 hV).2.2 S hS
    rw [Finset.sum_congr rfl h2, Finset.sum_comm, ← Finset.sum_coe_sort Q]
    exact Finset.sum_congr rfl fun S _ => h1 S
  have hrho : Module.finrank ℚ (LinearMap.range (branchClassMap
      (fun S : Q => primeDivisorNormalizationScheme S.1) Br (fun S b => b.1))) ≤
      ∑ S ∈ Q, (letI := primeDivisorNormalizationOver sY S
        haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
        MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S)) := by
    have hNp : ∀ S : Q, IsProjective (primeDivisorNormalizationScheme S.1 ↘ Spec (.of ℂ)) :=
      fun S => IsProjectiveMorphism.isProjective (hN S).isProjective
    haveI : ∀ S : Q, FiniteDimensional ℚ (divisorClasses (primeDivisorNormalizationScheme S.1)) :=
      fun S => (finrank_divisorClasses_le_divisorCycleRank _ (hNp S)).1
    let ψ : ↥(LinearMap.range (branchClassMap (fun S : Q => primeDivisorNormalizationScheme S.1)
        Br (fun S b => b.1))) →ₗ[ℚ]
        (∀ S : Q, divisorClasses (primeDivisorNormalizationScheme S.1)) :=
      LinearMap.pi fun S => ((LinearMap.proj S).comp (Submodule.subtype _)).codRestrict _
        (fun x => by
          obtain ⟨u, hu⟩ := x.2
          change x.1 S ∈ _
          rw [← hu]
          exact ⟨_, rfl⟩)
    have hψ : Function.Injective ψ := by
      intro x y hxy
      exact Subtype.ext (funext fun S => congrArg Subtype.val (congrFun hxy S))
    refine (LinearMap.finrank_le_finrank_of_injective hψ).trans ?_
    rw [Module.finrank_pi_fintype, ← Finset.sum_coe_sort Q]
    exact Finset.sum_le_sum fun S _ => (finrank_divisorClasses_le_divisorCycleRank _ (hNp S)).2
  rw [hcount, h𝒱card] at hmain
  have h1 : ∀ V ∈ 𝒱fin, 1 ≤ boundaryBranchCount Q V := fun V hV => ((h𝒱 V).1 hV).2.2.le
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  have : (∑ V ∈ 𝒱fin, (boundaryBranchCount Q V : ℤ)) ≤ 𝒱fin.card +
      (∑ S ∈ Q, (letI := primeDivisorNormalizationOver sY S
        haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
        MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
      Module.finrank ℚ (verticalDefectOver r F (Qd.supp : Set Y)) := by
    exact_mod_cast hmain.trans (by gcongr)
  linarith

end Key

/-- On a curve-and-point exceptional model of `Y`, every singular point of `Y` lies over the image
of an exceptional component, so its closure has dimension at most one. -/
private lemma topologicalKrullDim_closure_le_one_of_notMem_smoothLocus {Z Y : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (y : Y) (hy : y ∉ smoothLocus sY) :
    topologicalKrullDim (closure ({y} : Set Y)) ≤ 1 := by
  have hres := hM.isResolution
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hres.2.2.2.1
  haveI : IsIntegral Z := hres.2.1.toIsIntegral
  obtain ⟨z, rfl⟩ := surjective_of_isBirationalMorphism r r.isClosedMap hres.2.2.2.2 y
  have hz : z ∈ (F.supp : Set Z) := by rw [hM.supp_eq_preimage_singularLocus]; exact hy
  rw [ConductorBlowup.coe_supp_eq_iUnion] at hz
  obtain ⟨E, hE, hzE⟩ := Set.mem_iUnion₂.1 hz
  exact le_trans (topologicalKrullDim_mono' (closure_minimal
    (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ hzE)) (r.isClosedMap _
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support E))))
    (hM.topologicalKrullDim_image_le E hE)

/-- The branch excess of `Q` is the finite sum over the surfaces with several branches. -/
private lemma finsum_boundaryBranchCount_sub_one_eq_sum {Y : Scheme.{0}}
    (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (hbr1 : ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 2 →
      (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) → 1 ≤ boundaryBranchCount Q V)
    (hbrfin : {V : IrreducibleCloseds Y | topologicalKrullDim (V : Set Y) = 2 ∧
      (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q V}.Finite) :
    ∑ᶠ (V : IrreducibleCloseds Y) (_ : topologicalKrullDim (V : Set Y) = 2 ∧
      (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), ((boundaryBranchCount Q V : ℤ) - 1) =
      ∑ V ∈ hbrfin.toFinset, ((boundaryBranchCount Q V : ℤ) - 1) := by
  change ∑ᶠ V ∈ {V : IrreducibleCloseds Y | topologicalKrullDim (V : Set Y) = 2 ∧
    (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)}, ((boundaryBranchCount Q V : ℤ) - 1) = _
  rw [← finsum_mem_inter_support]
  have hset : {V : IrreducibleCloseds Y | topologicalKrullDim (V : Set Y) = 2 ∧
      (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)} ∩
      Function.support (fun V : IrreducibleCloseds Y => ((boundaryBranchCount Q V : ℤ) - 1)) =
      (hbrfin.toFinset : Set (IrreducibleCloseds Y)) := by
    rw [Set.Finite.coe_toFinset]
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, ne_eq, sub_eq_zero]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, lt_of_le_of_ne (hbr1 V h1 h2) (fun h => h3 (by exact_mod_cast h.symm))⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun h => (ne_of_gt h3) (by exact_mod_cast h)⟩
  rw [hset, finsum_mem_coe_finset]

/-- The sum of the prime divisors in `Q` is a reduced effective divisor supported on `⋃ Q`. -/
private lemma isReducedEffective_sum_single_and_coe_supp {Y : Scheme.{0}}
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) :
    MMP.Intersection.IsReducedEffective (∑ S ∈ Q, Finsupp.single S 1 : Divisor Y) ∧
      ((∑ S ∈ Q, Finsupp.single S 1 : Divisor Y).supp : Set Y) =
        ⋃ S ∈ Q, (S.support : Set Y) := by
  classical
  let Qd : Divisor Y := ∑ S ∈ Q, Finsupp.single S 1
  have hQd_coeff : ∀ S, Qd S = if S ∈ Q then 1 else 0 := by
    intro S
    simp only [Qd, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  refine ⟨fun S => ?_, ?_⟩
  · change Qd S = 0 ∨ Qd S = 1
    rw [hQd_coeff]
    split_ifs <;> simp
  · change (Qd.supp : Set Y) = _
    rw [MMP.Mori.DivisorWithCoeffs.coe_supp]
    ext y
    simp only [Set.mem_iUnion, Finsupp.mem_support_iff, hQd_coeff]
    constructor
    · rintro ⟨S, hS, hy⟩
      exact ⟨S, by by_contra h; simp [h] at hS, hy⟩
    · rintro ⟨S, hS, hy⟩
      exact ⟨S, by simp [hS], hy⟩

open MMP MMP.Fourfold.ConductorBlowup in
/-- The exceptional set of a resolution of a `ℚ`-factorial `Y`, inside an snc closed subset, is
the support of a reduced snc divisor. -/
private lemma exists_reducedDivisor_supp_eq_exceptionalSet {Y Z : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    [IsLocallyNoetherian Z] {sY : Y ⟶ Spec (.of ℂ)} (hYQ : IsQFactorial sY) {r : Z ⟶ Y}
    (hcompr : r ≫ sY = Z ↘ Spec (.of ℂ)) (hres : MMP.Intersection.IsResolution sY r)
    {A : Set Z}
    (hsnc : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) (A ∪ exceptionalSet r)) :
    ∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
      DivisorWithCoeffs.IsSNC (r ≫ sY) F ∧ (F.supp : Set Z) = exceptionalSet r := by
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  obtain ⟨F, hFred, hFsnc, hFsupp⟩ := exists_reducedDivisor_of_subset (hcompr ▸ hres.2.2.1)
    hsnc (exceptionalSet r).isClosed
    (MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial sY (r ≫ sY) hYQ hres.2.1 r rfl
      hres.2.2.2.1 hres.2.2.2.2) Set.subset_union_right
  exact ⟨F, hFred, hcompr ▸ hFsnc, hFsupp⟩

end Proof_thm_mmp_conductor_branch_bound_without_weights

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

open Proof_thm_mmp_conductor_branch_bound_without_weights MMP MMP.Fourfold.ConductorBlowup
  MMP.UnderlyingSpace in
open scoped MMP.SubschemeOver in
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **Branch bound by exceptional defects.** Let `p : Y ⟶ X` be a projective birational
morphism of normal projective complex fourfolds, with `Y` `ℚ`-factorial and terminal. Let `Q` be
a finite set of prime divisors of `Y` whose union has image of dimension at most one under `p`.
Then every irreducible curve `T ⊆ Sing Y` has a local-system open `T° ⊆ T`, and for these
`∑_{V ⊆ Q} (r_V - 1) ≤ ∑_{S ∈ Q} ρ_*(S^ν) + ∑_{T ⊆ Sing Y ∩ Q} b_T`, with `V` over the
irreducible surfaces contained in `Q`, `r_V = boundaryBranchCount Q V`,
`ρ_*(S^ν) = MMP.Analytic.divisorCycleRank` of the normalization of `S`, and
`b_T = curveLocalSystemRank sY T°`. -/
@[mmp "thm_mmp_conductor_branch_bound_without_weights"]
public theorem sum_boundaryBranchCount_sub_one_le_sum_curveLocalSystemRank
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 4)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 4)
    (hYQ : IsQFactorial sY) (hYt : IsTerminalVariety sY)
    (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (hpQ : topologicalKrullDim (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) ≤ 1) :
    ∃ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
    (∀ T, IsLocalSystemOpen sY (To T)) ∧
    ∑ᶠ (V : IrreducibleCloseds Y) (_ : topologicalKrullDim (V : Set Y) = 2 ∧
        (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), ((boundaryBranchCount Q V : ℤ) - 1) ≤
      ((∑ S ∈ Q,
          letI := primeDivisorNormalizationOver sY S
          haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
        ((∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)),
          curveLocalSystemRank sY (To T) : ℕ) : ℤ) := by
  classical
  -- the surfaces with several branches
  obtain ⟨hbr1, hbrfin⟩ := one_le_boundaryBranchCount_and_finite_setOf_one_lt sY hYQ.1 hYdim Q
  rw [finsum_boundaryBranchCount_sub_one_eq_sum Q hbr1 hbrfin]
  -- `Q` as a reduced divisor
  let Qd : Divisor Y := ∑ S ∈ Q, Finsupp.single S 1
  obtain ⟨hQd, hQdsupp⟩ : MMP.Intersection.IsReducedEffective Qd ∧
      (Qd.supp : Set Y) = ⋃ S ∈ Q, (S.support : Set Y) :=
    isReducedEffective_sum_single_and_coe_supp Q
  -- the simultaneous conductor model
  obtain ⟨Z₀, _, _, _, _, r₀, F₀, D₀, hM₀, Bs, hBs, hBsnc, Z, _, _, _, _, _, q, e, hq, hcomp,
      hres, hsnc1, hsnc2, hD, hprinc, -, -, hbound⟩ :=
    exists_isCurvePointExceptionalModel_finrank_verticalDefectOver_le hp hXproj hXdim
      ⟨hpproj, hpbir⟩ hYproj hYQ hYdim hYt hQd (hQdsupp ▸ hpQ) (hbrfin.toFinset : Set _)
      (Finset.finite_toSet _)
  -- the reduced exceptional divisor of `r = q ≫ r₀`
  obtain ⟨F, hFred, hFsnc, hFsupp⟩ : ∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
      DivisorWithCoeffs.IsSNC ((q ≫ r₀) ≫ sY) F ∧ (F.supp : Set Z) = exceptionalSet (q ≫ r₀) :=
    exists_reducedDivisor_supp_eq_exceptionalSet hYQ (by rw [Category.assoc]; exact hcomp) hres
      hsnc1
  -- local-system opens of the singular curves, from adapted opens for the resolution `r₀`
  have hTo_ex : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1},
      ∃ To : (curveScheme T.1).Opens, IsLocalSystemOpen sY To := fun T => by
    obtain ⟨To, hTo⟩ := (IsLocalSetting.exists_isAdaptedOpen_and_isAdaptedOpen_of_le
      (Θ := 0) (π := r₀) ⟨hYQ, hYproj, hYdim, hYt, T.2.2, T.2.1, hM₀.isResolution,
        hM₀.isBiregular⟩).1
    exact ⟨To, hTo.toIsLocalSystemOpen⟩
  choose To hTo using hTo_ex
  refine ⟨To, hTo, ?_⟩
  have hb := hbound F hFred hFsupp To hTo
  rw [hQdsupp] at hb
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYproj.toIsVariety.toLocallyOfFiniteType
  haveI : (q ≫ r₀).IsOver (Spec (.of ℂ)) := ⟨(Category.assoc _ _ _).trans hcomp⟩
  haveI : IsProper (q ≫ r₀) := isProper_of_isProjectiveMorphism _ hres.2.2.2.1
  have key : ∑ V ∈ hbrfin.toFinset, ((boundaryBranchCount Q V : ℤ) - 1) ≤
      ((∑ S ∈ Q,
          letI := primeDivisorNormalizationOver sY S
          haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℕ) : ℤ) +
        (Module.finrank ℚ (verticalDefectOver (q ≫ r₀) F (Qd.supp : Set Y)) : ℤ) :=
    sum_boundaryBranchCount_sub_one_le_finrank_verticalDefectOver sX sY hX hXproj hXdim
      p hp hpproj hpbir hYproj hYdim hYQ Q hpQ
      hbrfin.toFinset (fun V => Set.Finite.mem_toFinset hbrfin) Qd hQd hQdsupp
      (topologicalKrullDim_closure_le_one_of_notMem_smoothLocus hM₀) (q ≫ r₀)
      (by rw [Category.assoc]; exact hcomp) hres hsnc1 hsnc2 hD hprinc F hFred hFsnc hFsupp
  rw [hQdsupp] at key
  exact key.trans (by gcongr)

end MMP.Fourfold
