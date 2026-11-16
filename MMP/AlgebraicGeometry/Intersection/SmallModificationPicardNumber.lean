module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite

/-!
# Small modifications preserve the Picard number

Let `X`, `Y` be normal `ℚ`-factorial projective varieties over an algebraically closed field `k`
of characteristic zero which are isomorphic outside closed subsets of codimension at least two:
there are closed `V ⊆ X`, `W ⊆ Y` with `codim V, codim W ≥ 2` and an isomorphism
`X ∖ V ≅ Y ∖ W` over `k`. Then `ρ(X) = ρ(Y)`.

The isomorphism `X ∖ V ≅ Y ∖ W` matches the prime divisors of `X` and `Y`, since their generic
points avoid `V` and `W`; this gives the strict transform `QDivisor X ≃ QDivisor Y`. It
preserves numerical triviality: on a smooth projective common resolution `p : T ⟶ X`,
`q : T ⟶ Y`, for `D ≡ 0` on `X` with strict transform `D'`, the difference `F = p^*D - q^*D'`
has `q_* F = 0` and degree zero on every curve contracted by `q`, so the negativity lemma applied
to `F` and `-F` gives `q^*D' = p^*D`; lifting a proper curve `C ⊆ Y` to `T` and the projection
formula then give `(D' · C) = 0`. Finally `ρ = dim_ℝ N₁` is the rational dimension of the space of
`ℚ`-divisors modulo numerically trivial ones: choosing rational forms which are a basis of the
intersection numbers identifies the real quotient by the annihilator with a real space of the same
dimension.

## Main results

* `MMP.Fourfold.picardNumber_eq_of_isoInCodimOne`: `ρ(X) = ρ(Y)`.

## Implementation notes

The birational map is recorded by the isomorphism `e : X ∖ V ≅ Y ∖ W` of its domain of
definition and image, compatible with the structure morphisms; since the complements are proper
closed subsets of irreducible schemes, `e` is a birational map. The Picard number is
`MMP.Mori.picardNumber`, `dim_ℝ N₁`. The ground field is an algebraically closed field of
characteristic zero rather than `ℂ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-! ### Real ranks of quotients cut out by rational forms -/

section LinearAlgebra

variable {ι : Type}

/-- The pairing `(s, c) ↦ ∑ᵢ cᵢ s(i)` of a rational function `s` on `ι` with a finitely
supported real function `c` on `ι`. -/
private noncomputable def pairing : (ι → ℚ) →ₗ[ℚ] ((ι →₀ ℝ) →ₗ[ℝ] ℝ) where
  toFun s := Finsupp.linearCombination ℝ (fun i => (s i : ℝ))
  map_add' s t := by ext i; simp
  map_smul' q s := by ext i; simp [Rat.smul_def]

private theorem pairing_single (s : ι → ℚ) (i : ι) (r : ℝ) :
    pairing s (Finsupp.single i r) = r * s i := by
  simp [pairing]

private theorem pairing_mapRange (s : ι → ℚ) (c : ι →₀ ℚ) :
    pairing s (c.mapRange (Rat.cast : ℚ → ℝ) Rat.cast_zero) =
      ((Finsupp.linearCombination ℚ s c : ℚ) : ℝ) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [Finsupp.mapRange_add (by simp), map_add, hc, hd, map_add, Rat.cast_add]
  | single i r => simp [pairing]

/-- Pairing with `n` rationally independent rational functions maps the real finitely supported
functions onto `ℝⁿ`. -/
private theorem surjective_pi_pairing {n : ℕ} (s : Fin n → ι → ℚ) (hs : LinearIndependent ℚ s) :
    Function.Surjective (LinearMap.pi fun j => pairing (s j)) := by
  classical
  let T : (ι →₀ ℚ) →ₗ[ℚ] (Fin n → ℚ) := LinearMap.pi fun j => Finsupp.linearCombination ℚ (s j)
  have hT : LinearMap.range T = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let a : Fin n → ℚ := fun j => f (Pi.single j 1)
    have hfa : ∀ v, f v = ∑ j, a j * v j := by
      intro v
      conv_lhs => rw [show v = ∑ j, v j • Pi.single j (1 : ℚ) by
        ext i; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, a, mul_comm]
    have hsum : ∑ j, a j • s j = 0 := by
      funext i
      have := hf (LinearMap.mem_range_self T (Finsupp.single i 1))
      rw [LinearMap.mem_ker, hfa] at this
      simpa [T, Finset.sum_apply] using this
    have ha := (Fintype.linearIndependent_iff.mp hs) a hsum
    exact hf0 (LinearMap.ext fun v => by simp [hfa, ha])
  rw [← LinearMap.range_eq_top]
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun ℝ (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp hT (Pi.single j 1)
  refine ⟨c.mapRange (Rat.cast : ℚ → ℝ) Rat.cast_zero, funext fun j' => ?_⟩
  have := congrFun hc j'
  simp only [T, LinearMap.pi_apply] at this
  simp only [LinearMap.pi_apply, pairing_mapRange, this, Pi.basisFun_apply]
  obtain rfl | h := eq_or_ne j' j
  · simp
  · simp [Pi.single_apply, h]

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (Ψ : M →ₗ[ℚ] (ι → ℚ))

/-- The real finitely supported functions on `ι` killed by every rational function in the range
of `Ψ`. -/
private noncomputable def annihilator : Submodule ℝ (ι →₀ ℝ) :=
  ⨅ m, LinearMap.ker (pairing (Ψ m))

private theorem mem_annihilator {c : ι →₀ ℝ} :
    c ∈ annihilator Ψ ↔ ∀ m, pairing (Ψ m) c = 0 := by
  simp [annihilator]

private theorem le_rank_quotient {n : ℕ} (s : Fin n → ι → ℚ) (hs : LinearIndependent ℚ s)
    (hsΨ : ∀ j, s j ∈ LinearMap.range Ψ) :
    (n : Cardinal) ≤ Module.rank ℝ ((ι →₀ ℝ) ⧸ annihilator Ψ) := by
  have hK : annihilator Ψ ≤ LinearMap.ker (LinearMap.pi fun j => pairing (s j)) := by
    intro c hc
    rw [mem_annihilator] at hc
    refine LinearMap.mem_ker.mpr (funext fun j => ?_)
    obtain ⟨m, hm⟩ := hsΨ j
    simpa [← hm] using hc m
  have hsurj : Function.Surjective ((annihilator Ψ).liftQ _ hK) := by
    intro v
    obtain ⟨c, rfl⟩ := surjective_pi_pairing s hs v
    exact ⟨Submodule.Quotient.mk c, rfl⟩
  simpa using LinearMap.rank_le_of_surjective _ hsurj

private theorem rank_quotient_le {n : ℕ} (b : Module.Basis (Fin n) ℚ (LinearMap.range Ψ)) :
    Module.rank ℝ ((ι →₀ ℝ) ⧸ annihilator Ψ) ≤ n := by
  let R := LinearMap.pi fun j => pairing (b j : ι → ℚ)
  have hK : annihilator Ψ ≤ LinearMap.ker R := by
    intro c hc
    rw [mem_annihilator] at hc
    refine LinearMap.mem_ker.mpr (funext fun j => ?_)
    obtain ⟨m, hm⟩ := (b j).2
    simpa [R, ← hm] using hc m
  have hK' : LinearMap.ker R ≤ annihilator Ψ := by
    intro c hc
    rw [mem_annihilator]
    intro m
    have hsum := congrArg (fun x : LinearMap.range Ψ => (x : ι → ℚ))
      (b.sum_repr ⟨Ψ m, LinearMap.mem_range_self Ψ m⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply,
      show pairing (b j : ι → ℚ) c = 0 from congrFun (LinearMap.mem_ker.mp hc) j, smul_zero]
  have hinj : Function.Injective ((annihilator Ψ).liftQ R hK) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, eq_bot_iff]
    refine (Submodule.map_mono hK').trans ?_
    rw [Submodule.mkQ_map_self]
  simpa using LinearMap.rank_le_of_injective _ hinj

/-- **Real rank against rational rank.** For a `ℚ`-linear map `Ψ` into the rational functions on
`ι`, the real functions on `ι` with finite support modulo those killed by every function in the
range of `Ψ` have real dimension the rational dimension of the range of `Ψ`. -/
private theorem toENat_rank_quotient_annihilator :
    (Module.rank ℝ ((ι →₀ ℝ) ⧸ annihilator Ψ)).toENat =
      (Module.rank ℚ (LinearMap.range Ψ)).toENat := by
  by_cases hfin : Module.rank ℚ (LinearMap.range Ψ) < Cardinal.aleph0
  · have : Module.Finite ℚ (LinearMap.range Ψ) := Module.rank_lt_aleph0_iff.mp hfin
    let b := Module.finBasis ℚ (LinearMap.range Ψ)
    have h1 := rank_quotient_le Ψ b
    have h2 := le_rank_quotient Ψ (fun j => (b j : ι → ℚ))
      (LinearIndependent.map' b.linearIndependent (LinearMap.range Ψ).subtype
        (Submodule.ker_subtype _)) (fun j => (b j).2)
    rw [le_antisymm h1 h2, ← Module.finrank_eq_rank]
  · rw [not_lt] at hfin
    rw [Cardinal.toENat_eq_top.mpr hfin, Cardinal.toENat_eq_top]
    refine Cardinal.aleph0_le.mpr fun n => ?_
    let b := Module.Free.chooseBasis ℚ (LinearMap.range Ψ)
    have : Infinite (Module.Free.ChooseBasisIndex ℚ (LinearMap.range Ψ)) := by
      rwa [Cardinal.infinite_iff, b.mk_eq_rank'']
    let f : Fin n ↪ Module.Free.ChooseBasisIndex ℚ (LinearMap.range Ψ) :=
      Fin.valEmbedding.trans
        (Infinite.natEmbedding (Module.Free.ChooseBasisIndex ℚ (LinearMap.range Ψ)))
    exact le_rank_quotient Ψ (fun j => (b (f j) : ι → ℚ))
      ((b.linearIndependent.comp f f.injective).map' (LinearMap.range Ψ).subtype
        (Submodule.ker_subtype _)) (fun j => (b (f j)).2)

end LinearAlgebra

/-! ### Intersection numbers with curves and the Picard number -/

section CurveIntersection

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The intersection numbers `C ↦ (D · C)` of a `ℚ`-divisor `D` with the proper curves of `X`,
on a scheme where every `ℚ`-divisor is `ℚ`-Cartier. -/
private noncomputable def curveIntersection (hQ : ∀ D : QDivisor X, D.IsQCartier) :
    QDivisor X →ₗ[ℚ] (ProperCurve sX → ℚ) where
  toFun D C := D.intersectionNumber k sX C.ι C.dim_le (hQ D)
  map_add' D D' := funext fun C =>
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' (hQ D) (hQ D') (hQ _)
  map_smul' q D := funext fun C =>
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D (hQ D) (hQ _)

private theorem curveIntersection_apply (hQ : ∀ D : QDivisor X, D.IsQCartier) (D : QDivisor X)
    (C : ProperCurve sX) :
    curveIntersection sX hQ D C = D.intersectionNumber k sX C.ι C.dim_le (hQ D) :=
  rfl

/-- Pairing the intersection numbers of `D` with a real 1-cycle `Z` is `(D · [Z])`. -/
private theorem pairing_curveIntersection [CompactSpace X] (hQ : ∀ D : QDivisor X, D.IsQCartier)
    (D : QDivisor X) (Z : OneCycle ℝ sX) :
    pairing (curveIntersection sX hQ D) Z =
      QDivisor.curveForm sX D (hQ D) (OneCycle.numericalClass sX Z) := by
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add Z Z' h h' => rw [map_add, map_add, map_add, h, h']
  | single C r =>
    rw [pairing_single, show (Finsupp.single C r : OneCycle ℝ sX) = r • C.cycle ℝ by
        simp [ProperCurve.cycle], map_smul, map_smul,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle, smul_eq_mul, curveIntersection_apply]

/-- On an integral locally Noetherian scheme with Noetherian underlying space, every Cartier
divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier [IsIntegral X]
    [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  have h0 : ∀ x : X, Order.coheight x = 0 → x ∉ MMP.Intersection.cartierSupport A := by
    intro x hx
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
    have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A x
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) (fun s hs h0' => h0 s h0' hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- **Numerical triviality is detected by intersection numbers.** On an integral normal
Noetherian scheme on which every `ℚ`-divisor is `ℚ`-Cartier, a real 1-cycle is numerically
trivial exactly when `(D · Z) = 0` for every `ℚ`-divisor `D`. -/
private theorem numericallyTrivial_eq_annihilator [IsIntegral X] [CompactSpace X]
    [TopologicalSpace.NoetherianSpace X] (hQ : ∀ D : QDivisor X, D.IsQCartier) :
    OneCycle.numericallyTrivial sX = annihilator (curveIntersection sX hQ) := by
  ext Z
  rw [mem_annihilator]
  refine ⟨fun hZ D => ?_, fun hZ => ?_⟩
  · rw [pairing_curveIntersection, OneCycle.numericalClass, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr hZ, map_zero]
  · refine OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E
    have hwc : w.IsCartier := hw.isCartier
    obtain ⟨e'⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    have := hwc.isInvertibleModule_divisorialSheaf
    have key : OneCycle.degree ℝ sX L =
        pairing (curveIntersection sX hQ (Divisor.toQDivisor w)) := by
      refine Finsupp.lhom_ext fun C r => ?_
      rw [pairing_single, curveIntersection_apply,
        QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le w hwc]
      simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul, ProperCurve.degree]
      congr 2
      exact_mod_cast degreeOn_eq_of_iso k sX C.ι C.dim_le (e ≪≫ e')
    rw [key]
    exact hZ _

/-- **The Picard number is a rational rank.** On an integral normal Noetherian scheme proper over
`k` on which every `ℚ`-divisor is `ℚ`-Cartier, `ρ(X) = dim_ℝ N₁(X)` is the dimension over `ℚ` of
the space of `ℚ`-divisors modulo those of intersection number zero with every proper curve. -/
private theorem picardNumber_eq_toENat_rank [IsIntegral X] [CompactSpace X]
    [TopologicalSpace.NoetherianSpace X] (hQ : ∀ D : QDivisor X, D.IsQCartier) :
    picardNumber sX = (Module.rank ℚ (LinearMap.range (curveIntersection sX hQ))).toENat := by
  rw [← toENat_rank_quotient_annihilator, picardNumber,
    (Submodule.quotEquivOfEq _ _ (numericallyTrivial_eq_annihilator sX hQ)).rank_eq]

end CurveIntersection

/-! ### Prime divisors of schemes isomorphic in codimension one -/

section PrimeDivisors

/-- A morphism inducing an isomorphism of local rings at `x` preserves the coheight of `x`. -/
private theorem coheight_apply_of_isIso_stalkMap {A B : Scheme.{0}} (f : A ⟶ B) (a : A)
    [IsIso (f.stalkMap a)] : Order.coheight (f a) = Order.coheight a := by
  have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

variable {X Y : Scheme.{0}}

/-- The generic point of a prime divisor lies outside every closed subset of codimension at
least two. -/
private theorem genericPoint_mem_compl {V : Closeds X} (hV : 2 ≤ closedsCodimension V)
    (P : MMP.Mori.PrimeDivisor X) : P.genericPoint ∈ V.compl := by
  intro hP
  have h := le_closedsCodimension_iff.mp hV (IrreducibleCloseds.closureSingleton P.genericPoint)
    (closure_minimal (Set.singleton_subset_iff.mpr hP) V.isClosed)
  rw [MMP.Mori.PrimeDivisor.codimension_closure_genericPoint] at h
  exact absurd h (by norm_num)

/-- The point of `V.compl` at the generic point of a prime divisor. -/
private noncomputable def genericPointCompl {V : Closeds X} (hV : 2 ≤ closedsCodimension V)
    (P : MMP.Mori.PrimeDivisor X) : Scheme.Opens.toScheme (X := X) V.compl :=
  ⟨P.genericPoint, genericPoint_mem_compl hV P⟩

private theorem coheight_ι_hom_genericPointCompl {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (e : Scheme.Opens.toScheme (X := X) V.compl ≅
      Scheme.Opens.toScheme (X := Y) W.compl)
    (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (Scheme.Opens.ι (X := Y) W.compl (e.hom (genericPointCompl hV P))) = 1 := by
  have : IsOpenImmersion (e.hom ≫ Scheme.Opens.ι (X := Y) W.compl) := inferInstance
  have : IsIso ((e.hom ≫ Scheme.Opens.ι (X := Y) W.compl).stalkMap (genericPointCompl hV P)) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have : IsIso ((Scheme.Opens.ι (X := X) V.compl).stalkMap (genericPointCompl hV P)) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  rw [← Scheme.Hom.comp_apply, coheight_apply_of_isIso_stalkMap,
    ← coheight_apply_of_isIso_stalkMap (Scheme.Opens.ι (X := X) V.compl)]
  exact MMP.Mori.PrimeDivisor.coheight_genericPoint P

/-- The prime divisor of `Y` corresponding to a prime divisor `P` of `X` under an isomorphism
`X ∖ V ≅ Y ∖ W` with `codim V ≥ 2`: the closure of the image of the generic point of `P`. -/
private noncomputable def primeDivisorMap {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (e : Scheme.Opens.toScheme (X := X) V.compl ≅
      Scheme.Opens.toScheme (X := Y) W.compl)
    (P : MMP.Mori.PrimeDivisor X) : MMP.Mori.PrimeDivisor Y :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (coheight_ι_hom_genericPointCompl hV e P)

private theorem genericPoint_primeDivisorMap {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (e : Scheme.Opens.toScheme (X := X) V.compl ≅
      Scheme.Opens.toScheme (X := Y) W.compl)
    (P : MMP.Mori.PrimeDivisor X) :
    (primeDivisorMap hV e P).genericPoint =
      Scheme.Opens.ι (X := Y) W.compl (e.hom (genericPointCompl hV P)) :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

private theorem primeDivisorMap_symm_primeDivisorMap {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl)
    (P : MMP.Mori.PrimeDivisor X) :
    primeDivisorMap hW e.symm (primeDivisorMap hV e P) = P := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  show MMP.Mori.PrimeDivisor.genericPoint _ = MMP.Mori.PrimeDivisor.genericPoint _
  rw [genericPoint_primeDivisorMap]
  have : genericPointCompl hW (primeDivisorMap hV e P) = e.hom (genericPointCompl hV P) :=
    Subtype.ext (genericPoint_primeDivisorMap hV e P)
  rw [this, Iso.symm_hom, ← Scheme.Hom.comp_apply e.hom e.inv,
    Iso.hom_inv_id]
  rfl

/-- The bijection of prime divisors induced by an isomorphism `X ∖ V ≅ Y ∖ W` with
`codim V, codim W ≥ 2`. -/
private noncomputable def primeDivisorEquiv {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl) :
    MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor Y where
  toFun := primeDivisorMap hV e
  invFun := primeDivisorMap hW e.symm
  left_inv := primeDivisorMap_symm_primeDivisorMap hV hW e
  right_inv := primeDivisorMap_symm_primeDivisorMap hW hV e.symm

/-- The strict transform `QDivisor X ≃ QDivisor Y` along an isomorphism `X ∖ V ≅ Y ∖ W` with
`codim V, codim W ≥ 2`. -/
private noncomputable def strictTransform {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl) :
    QDivisor X ≃ₗ[ℚ] QDivisor Y :=
  Finsupp.domLCongr (primeDivisorEquiv hV hW e)

private theorem strictTransform_apply {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl)
    (D : QDivisor X) (P : MMP.Mori.PrimeDivisor Y) :
    strictTransform hV hW e D P = D ((primeDivisorEquiv hV hW e).symm P) := by
  simp [strictTransform, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

/-- The strict transform along `e⁻¹` inverts the strict transform along `e`. -/
private theorem strictTransform_symm_strictTransform {V : Closeds X} {W : Closeds Y}
    (hV : 2 ≤ closedsCodimension V) (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl)
    (D : QDivisor X) : strictTransform hW hV e.symm (strictTransform hV hW e D) = D := by
  refine Finsupp.ext fun P => ?_
  rw [strictTransform_apply, strictTransform_apply]
  exact congrArg D (primeDivisorMap_symm_primeDivisorMap hV hW e P)

end PrimeDivisors

/-! ### Intersection numbers of pulled-back `ℚ`-Cartier divisors -/

section Projection

variable {k : Type} [Field k] {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
  [QuasiCompact sV] [QuasiCompact sW] [CompactSpace V] [CompactSpace W] [IsIntegral V]
  [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W] [IsSeparated sW]
  [LocallyOfFiniteType sW]
  {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W} (hL : L.IsQCartier)
  {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp} {L' : QDivisor V}
  (h : L.IsPullback u hLB L')

include hu in
/-- The degree computation behind the projection formula: with `m` the Cartier index of `L` and
`D = mL`, `m (u^*L · C) = deg_C u^* 𝒪_W(D)`. -/
private theorem exists_intersectionNumber_isPullback_eq_degree_div (C : ProperCurve sV) :
    ∃ (D : Divisor W) (hDc : D.IsCartier),
      Divisor.toQDivisor D = ((L.cartierIndex hL : ℕ) : ℤ) • L ∧
      haveI := hDc.isInvertibleModule_divisorialSheaf
      L'.intersectionNumber k sV C.ι C.dim_le (h.isQCartier hL) =
        (C.degree k ((Scheme.Modules.pullback u).obj D.divisorialSheaf) : ℚ) /
          L.cartierIndex hL := by
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hL
  have hD'c := hp.isCartier hDc
  have := hDc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  refine ⟨D, hDc, hD, ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sV C.ι C.dim_le _ _ (QDivisor.cartierIndex_pos hL)
    D' hD'c hD', Divisor.degreeOn, degreeOn_eq_of_iso k sV C.ι C.dim_le
    (hp.divisorialSheafIso (hBc := hDc))]
  rfl

include hu in
/-- **Projection formula for a pulled-back `ℚ`-Cartier divisor.** For a proper curve `C ⊆ V`
whose image `u(C)` is the proper curve `C' ⊆ W`, `(u^*L · C) = [k(C) : k(C')] · (L · C')`. -/
private theorem intersectionNumber_isPullback_eq_residueFieldDegree_mul (C : ProperCurve sV)
    (C' : ProperCurve sW) (hC' : u C.point = C'.point) :
    L'.intersectionNumber k sV C.ι C.dim_le (h.isQCartier hL) =
      (residueFieldDegree u C.point : ℚ) * L.intersectionNumber k sW C'.ι C'.dim_le hL := by
  obtain ⟨D, hDc, hD, hdeg⟩ := exists_intersectionNumber_isPullback_eq_degree_div hu hL h C
  have := hDc.isInvertibleModule_divisorialSheaf
  have hC : IsProperCurve sW (u C.point) := hC' ▸ C'.isProperCurve
  have hCC : (⟨u C.point, hC⟩ : ProperCurve sW) = C' := ProperCurve.ext hC'
  rw [hdeg, C.degree_pullback u hu, dif_pos hC, hCC,
    QDivisor.intersectionNumber_eq_of_smul k sW _ _ _ _ (QDivisor.cartierIndex_pos hL) D hDc hD]
  push_cast
  rw [mul_div_assoc]
  rfl

include hu in
/-- `(u^*L · C) = 0` for a proper curve `C ⊆ V` whose image is not a proper curve. -/
private theorem intersectionNumber_isPullback_eq_zero_of_not_isProperCurve (C : ProperCurve sV)
    (hC : ¬ IsProperCurve sW (u C.point)) :
    L'.intersectionNumber k sV C.ι C.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, hDc, hD, hdeg⟩ := exists_intersectionNumber_isPullback_eq_degree_div hu hL h C
  have := hDc.isInvertibleModule_divisorialSheaf
  rw [hdeg, C.degree_pullback u hu, dif_neg hC]
  simp

include hu in
/-- `(u^*L · C) = 0` for a proper curve `C ⊆ V` contracted by `u`. -/
private theorem intersectionNumber_isPullback_eq_zero_of_isContractedBy (C : ProperCurve sV)
    (hC : C.IsContractedBy u) :
    L'.intersectionNumber k sV C.ι C.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, hDc, hD, hdeg⟩ := exists_intersectionNumber_isPullback_eq_degree_div hu hL h C
  have := hDc.isInvertibleModule_divisorialSheaf
  rw [hdeg, C.degree_pullback_eq_zero_of_isContractedBy u hu hC]
  simp

include hu in
/-- `(u^*L · C) = 0` for every proper curve `C ⊆ V` if `(L · C') = 0` for every proper curve
`C' ⊆ W`. -/
private theorem intersectionNumber_isPullback_eq_zero
    (hL0 : ∀ C' : ProperCurve sW, L.intersectionNumber k sW C'.ι C'.dim_le hL = 0)
    (C : ProperCurve sV) :
    L'.intersectionNumber k sV C.ι C.dim_le (h.isQCartier hL) = 0 := by
  by_cases hC : IsProperCurve sW (u C.point)
  · rw [intersectionNumber_isPullback_eq_residueFieldDegree_mul hu hL h C ⟨u C.point, hC⟩ rfl, hL0,
      mul_zero]
  · exact intersectionNumber_isPullback_eq_zero_of_not_isProperCurve hu hL h C hC

end Projection

/-! ### Pull-backs and strict transforms on a common resolution -/

section StrictTransform

/-- Let `E ⊆ X`, `P ⊆ Y` be prime divisors with `f(η_E) = η_P` and `𝒪_{Y,P} ≅ 𝒪_{X,E}`. The
coefficient of `E` in the pull-back of a `ℚ`-Cartier `ℚ`-divisor `L` is the coefficient of `P`
in `L`. -/
private theorem coeff_eq_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (E : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor Y) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] {L : QDivisor Y} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : QDivisor X} (h : L.IsPullback f hB L') : L' E = L P := by
  have hm := QDivisor.cartierIndex_pos hL
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hc := MMP.Positivity.coeff_eq_of_isPullback E P heq hD₀c hp
  have h1 := congrArg (fun G : QDivisor X => G E) hD'
  have h2 := congrArg (fun G : QDivisor Y => G P) hD₀
  simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1 h2
  have hm' : (L.cartierIndex hL : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine mul_left_cancel₀ hm' (h1.symm.trans (Eq.trans ?_ h2))
  exact congrArg (fun z : ℤ => (z : ℚ)) hc

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_self_of_toRationalMap_eq_symm {X Y : Scheme.{0}} [IsReduced Y]
    [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- A separated birational morphism `f : T ⟶ X` of integral schemes has at most one point over
the generic point of a prime divisor `P` of the normal scheme `X`: the local ring of `P` is a
valuation ring of the common function field, so it is the local ring of any such point. -/
private theorem eq_of_apply_eq_genericPoint {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] (f : T ⟶ X) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (P : MMP.Mori.PrimeDivisor X)
    {x₁ x₂ : T} (h₁ : f x₁ = P.genericPoint) (h₂ : f x₂ = P.genericPoint) : x₁ = x₂ := by
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (f x₁)) := h₁ ▸ inferInstance
  haveI : ValuationRing (X.presheaf.stalk (f x₂)) := h₂ ▸ inferInstance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- **The strict transform on a resolution.** Let `p : T ⟶ X` be a proper birational morphism
of normal varieties with inverse `h`, and `P` a prime divisor of `X`. Then `h` is defined at `η_P`
by some `h'`, and `h'(η_P)` is the generic point of a prime divisor `E` of `T` with
`p(η_E) = η_P`, along which `p` induces an isomorphism of local rings. -/
private theorem exists_strictTransform {k : Type} [Field k] {X T : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (hX : IsNormalVariety k sX) (p : T ⟶ X)
    (h : X.RationalMap T) [IsProper p] (hTp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor T) (h' : X.PartialMap T) (hP : P.genericPoint ∈ h'.domain),
      h'.toRationalMap = h ∧ E.genericPoint = h'.hom ⟨P.genericPoint, hP⟩ ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hTp.1
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sX
  have : IsSeparated p := IsSeparated.of_comp p sX
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hTp hpb P
  obtain ⟨e, he1, he2⟩ := id hinv
  have hhp : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
    rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨h', hh'P, hh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      P.coheight_genericPoint.le)
  have hpw : p (h'.hom ⟨P.genericPoint, hh'P⟩) = P.genericPoint :=
    apply_hom_eq_self_of_toRationalMap_eq_symm p e he1 h' (hh'.trans he2.symm) hh'P
  exact ⟨E, h', hh'P, hh',
    eq_of_apply_eq_genericPoint p hpb.functionFieldMap_bijective P heq hpw, heq, hiso⟩

end StrictTransform

/-! ### Relative nefness and contracted curves -/

section Contracted

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The sum defining relative nefness of a `ℚ`-Cartier `ℚ`-divisor is its intersection number. -/
private theorem sum_associatedCartier_eq_intersectionNumber [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] (D : QDivisor X) (h : D.IsQCartier)
    (C : ProperCurve sX) :
    ((D.associatedCartier h).sum fun E c =>
      (c : ℝ) * ((E : Divisor X).degreeOn k sX C.ι C.dim_le E.2 : ℝ)) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.sum_single_index (by simp),
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D h _
      (D.cartierIndexSMul h).2 (QDivisor.toQDivisor_cartierIndexSMul D h)]
  push_cast
  ring

/-- A `ℚ`-Cartier `ℚ`-divisor is `f`-nef as soon as its intersection number with every proper
curve contracted by `f` is nonnegative. -/
private theorem isRelativelyNef_of_forall_intersectionNumber_nonneg [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Y) (D : QDivisor X) (h : D.IsQCartier)
    (hD : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le h) :
    D.IsRelativelyNef sX f :=
  ⟨h, fun C hC => by
    rw [sum_associatedCartier_eq_intersectionNumber]
    exact_mod_cast hD C hC⟩

/-- **Negativity on both signs.** Let `q : T ⟶ Y` be a proper birational morphism of normal
varieties with every `ℚ`-divisor of `T` `ℚ`-Cartier. A `ℚ`-divisor `F` on `T` with `q_* F = 0`
and `(F · C) = 0` for every curve `C` contracted by `q` is zero: the negativity lemma applied to
`F` and to `-F` makes both effective. -/
private theorem eq_zero_of_transformDivisor_eq_zero {T : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    {sT : T ⟶ Spec (.of k)} [QuasiCompact sT] [IsLocallyNoetherian T] [IsNormal T]
    (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT) (q : T ⟶ Y) (hq : q ≫ sY = sT)
    [IsProper q] (hqb : IsBirationalMorphism q) (hQ : ∀ G : QDivisor T, G.IsQCartier)
    {F : QDivisor T} (hqF : RationalMap.transformDivisor (X := T) q.toRationalMap F = 0)
    (hF : ∀ C : ProperCurve sT, C.IsContractedBy q → curveIntersection sT hQ F C = 0) :
    F = 0 := by
  have hnef : ∀ G : QDivisor T, (∀ C : ProperCurve sT, C.IsContractedBy q →
      curveIntersection sT hQ G C = 0) → G.IsRelativelyNef sT q :=
    fun G hG =>
      isRelativelyNef_of_forall_intersectionNumber_nonneg q G (hQ G) fun C hC => (hG C hC).ge
  have h1 : F.IsEffective :=
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg k sY sT hY hT q hq
      hqb (hQ F) (hnef _ fun C hC => by rw [map_neg, Pi.neg_apply, hF C hC, neg_zero])
      (hqF ▸ DivisorWithCoeffs.isEffective_zero)
  have h2 : (-F).IsEffective :=
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg k sY sT hY hT q hq
      hqb (hQ _) ((neg_neg F).symm ▸ hnef F hF)
      (by
        rw [map_neg, hqF, neg_zero]
        exact DivisorWithCoeffs.isEffective_zero)
  refine Finsupp.ext fun E => le_antisymm ?_ (h1 E)
  simpa [DivisorWithCoeffs.coeff] using h2 E

variable {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- If `g` maps the closure of `Γ` onto the closure of a proper curve `C ⊆ Y`, then `g` does not
contract `Γ`. -/
private theorem not_isContractedBy_of_image_closure_eq {g : X ⟶ Y} {Γ : ProperCurve sX}
    {C : ProperCurve sY} (h : g '' closure {Γ.point} = closure {C.point}) :
    ¬ Γ.IsContractedBy g := by
  intro hc
  have hsub : closure ({C.point} : Set Y) ⊆ {g Γ.point} := by
    rw [← h]
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hr : ∀ t, curveSubschemeAtι C.point t = g Γ.point := fun t => by
    have ht : curveSubschemeAtι C.point t ∈ closure {C.point} :=
      range_curveSubschemeAtι C.point ▸ ⟨t, rfl⟩
    exact hsub ht
  have : Subsingleton (curveSubschemeAt C.point) :=
    ⟨fun a b => (curveSubschemeAtι C.point).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h1 := C.dim_eq
  have h0 : topologicalKrullDim (curveSubschemeAt C.point) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [show ProperCurve.scheme C = curveSubschemeAt C.point from rfl, h1] at *
  norm_num at h0

end Contracted

/-! ### Numerical triviality is preserved by small modifications -/

section Transfer

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}

/-- The partial isomorphism `X ⤏ Y` of an isomorphism `X ∖ V ≅ Y ∖ W`, `V`, `W` of codimension
at least two in irreducible schemes. -/
private noncomputable def partialIsoOfCompl [IrreducibleSpace X] [IrreducibleSpace Y]
    {V : Closeds X} {W : Closeds Y} (hV : 2 ≤ closedsCodimension V)
    (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl) :
    X.PartialIso Y where
  source := V.compl
  dense_source := V.compl.isOpen.dense (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V hV)
  target := W.compl
  dense_target := W.compl.isOpen.dense (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W hW)
  iso := e

/-- The birational map of an isomorphism `X ∖ V ≅ Y ∖ W` over `k` is a modification of the
structure morphisms. -/
private theorem isModificationOf_partialIsoOfCompl [IrreducibleSpace X] [IrreducibleSpace Y]
    {V : Closeds X} {W : Closeds Y} (hV : 2 ≤ closedsCodimension V)
    (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl)
    (he : e.hom ≫ Scheme.Opens.ι (X := Y) W.compl ≫ sY = Scheme.Opens.ι (X := X) V.compl ≫ sX) :
    MMP.Flips.IsModificationOf sX sY (partialIsoOfCompl hV hW e).toRationalMap := by
  refine ⟨⟨_, rfl⟩, ?_⟩
  change (partialIsoOfCompl hV hW e).toRationalMap.compHom sY = sX.toRationalMap
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨V.compl, (partialIsoOfCompl hV hW e).dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_refl V.compl) ≫ (e.hom ≫ Scheme.Opens.ι (X := Y) W.compl) ≫ sY =
    X.homOfLE (le_top : V.compl ≤ ⊤) ≫ X.topIso.hom ≫ sX
  rw [Scheme.homOfLE_rfl, Category.id_comp, Category.assoc, he, Scheme.topIso_hom,
    Scheme.homOfLE_ι_assoc]

/-- **Numerical triviality is preserved by small modifications.** If `X`, `Y` are normal
`ℚ`-factorial projective varieties over a field of characteristic zero isomorphic outside
closed subsets of codimension at least two, the strict transform of a numerically trivial
`ℚ`-divisor on `X` is numerically trivial on `Y`. -/
private theorem intersectionNumber_strictTransform_eq_zero [CharZero k]
    (hX : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    {V : Closeds X} {W : Closeds Y} (hV : 2 ≤ closedsCodimension V)
    (hW : 2 ≤ closedsCodimension W)
    (e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := Y) W.compl)
    (he : e.hom ≫ Scheme.Opens.ι (X := Y) W.compl ≫ sY = Scheme.Opens.ι (X := X) V.compl ≫ sX)
    (D : QDivisor X)
    (hD : ∀ C : ProperCurve sX,
      D.intersectionNumber k sX C.ι C.dim_le (isQCartier_of_isQFactorial sX hX D) = 0)
    (C : ProperCurve sY) :
    (strictTransform hV hW e D).intersectionNumber k sY C.ι C.dim_le
      (isQCartier_of_isQFactorial sY hY _) = 0 := by
  have hXv := hX.1
  have hYv := hY.1
  have := hXv.1
  have := hYv.1
  have : IsIntegral X := hXv.1.toIsIntegral
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hXp.isProjective
  have : IsProper sY := isProper_of_isProjectiveMorphism sY hYp.isProjective
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  set σ := primeDivisorEquiv hV hW e
  set D' := strictTransform hV hW e D
  have hQX := isQCartier_of_isQFactorial sX hX
  have hQY := isQCartier_of_isQFactorial sY hY
  -- the common resolution
  obtain ⟨T, p, q, hTv, hTsm, hpP, hqP, hpb, hqb, ⟨ψ, hψinv, hψq⟩, hpq⟩ :=
    MMP.Flips.IsModificationOf.exists_smooth_common_model sX sY (𝟙 _) hXv hYv IsVariety.mk
      sX sY (Category.comp_id _) (Category.comp_id _) _
      (isModificationOf_partialIsoOfCompl hV hW e he)
  set sT := p ≫ sX with hsT
  have := hTv
  have : IsIntegral T := hTv.toIsIntegral
  have hTn' := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hTsm
  have := hTn'.1
  have := hTn'.2
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper p := hpP
  have : IsProper q := hqP
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have hTn : IsNormalVariety k sT := ⟨hTv, inferInstance⟩
  have hqs : q ≫ sY = sT := hpq.symm
  have hTnq : IsNormalVariety k (q ≫ sY) := hqs ▸ hTn
  have hQT : ∀ G : QDivisor T, G.IsQCartier := isQCartier_of_isQFactorial sT
    ⟨hTn, fun G => ⟨1, one_pos, by
      simpa using MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hTsm G⟩⟩
  -- strict transforms of prime divisors on the common resolution
  have hS1 : ∀ P : MMP.Mori.PrimeDivisor X, ∃ E : MMP.Mori.PrimeDivisor T,
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) ∧
      q E.genericPoint = (σ P).genericPoint := by
    intro P
    have := isSeparated_toTerminal sY
    obtain ⟨E, h', hh'P, hh', hwE, heq, hiso⟩ := exists_strictTransform hXv p ψ hTn hpb hψinv P
    refine ⟨E, heq, hiso, ?_⟩
    rw [hwE, show σ P = primeDivisorMap hV e P from rfl, genericPoint_primeDivisorMap]
    have hrat : (h'.compHom q).toRationalMap =
        (partialIsoOfCompl hV hW e).toPartialMap.toRationalMap := by
      rw [Scheme.RationalMap.compHom_toRationalMap, hh', hψq]
    exact MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat hh'P
      (genericPoint_mem_compl hV P)
  -- the two pull-backs
  set A := D.pullback (hQX D)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p D) with hA
  have hAp := QDivisor.isPullback_pullback (f := p) (hQX D)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p D)
  set B := D'.pullback (hQY D')
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q D') with hB
  have hBp := QDivisor.isPullback_pullback (f := q) (hQY D')
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q D')
  -- `q_* p^* D = D'`
  have hqA : RationalMap.transformDivisor (X := T) q.toRationalMap A = D' := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨E₀, heq₀, hiso₀, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYv hTnq hqb P
    rw [htr]
    obtain ⟨E, hpE, hpiso, hqE⟩ := hS1 (σ.symm P)
    rw [σ.apply_symm_apply] at hqE
    have : IsSeparated q := IsSeparated.of_comp q sY
    obtain rfl : E₀ = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq_genericPoint q hqb.functionFieldMap_bijective P heq₀ hqE)
    rw [coeff_eq_of_isPullback E₀ (σ.symm P) hpE (hQX D) hAp]
    exact (strictTransform_apply hV hW e D P).symm
  have hqB : RationalMap.transformDivisor (X := T) q.toRationalMap B = D' :=
    MMP.Positivity.transformDivisor_of_isPullback hYv hTnq hqb (hQY D') _ hBp
  -- `p^* D` has degree zero on every proper curve
  have hA0 : ∀ C : ProperCurve sT, curveIntersection sT hQT A C = 0 := fun C =>
    intersectionNumber_isPullback_eq_zero rfl (hQX D) hAp hD C
  -- negativity: `p^* D = q^* D'`
  have hAB : A = B := sub_eq_zero.mp <|
    eq_zero_of_transformDivisor_eq_zero sY hYv hTn q hqs hqb hQT
      (by rw [map_sub, hqA, hqB, sub_self]) fun C hC => by
        rw [map_sub, Pi.sub_apply, hA0, zero_sub, neg_eq_zero]
        exact intersectionNumber_isPullback_eq_zero_of_isContractedBy hqs (hQY D') hBp C hC
  -- lift `C` to a proper curve `C̃` of `T`: `0 = (q^* D' · C̃) = [k(C̃) : k(C)] (D' · C)`
  have : Surjective q := inferInstance
  obtain ⟨Ct, hCt⟩ := ProperCurve.exists_image_closure_eq_of_surjective hTv hYv.1 q hqs C
  have hpt : q Ct.point = C.point := by
    have h1 : closure {q Ct.point} = closure {C.point} := by
      rw [← hCt, ← Set.image_singleton, q.isClosedMap.closure_image_eq_of_continuous q.continuous]
    exact (inseparable_iff_closure_eq.mpr h1).eq
  have hpos := MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy q hqs Ct
    (not_isContractedBy_of_image_closure_eq hCt)
  have key : (residueFieldDegree q Ct.point : ℚ) *
      D'.intersectionNumber k sY C.ι C.dim_le (hQY D') = 0 :=
    (intersectionNumber_isPullback_eq_residueFieldDegree_mul hqs (hQY D') hBp Ct C hpt).symm.trans
      (show curveIntersection sT hQT B Ct = 0 from hAB ▸ hA0 Ct)
  exact (mul_eq_zero.mp key).resolve_left (by exact_mod_cast hpos.ne')

end Transfer

/-- **Small modifications preserve the Picard number.** Let `X`, `Y` be normal `ℚ`-factorial
projective varieties over an algebraically closed field `k` of characteristic zero, and let
`V ⊆ X`, `W ⊆ Y` be closed subsets of codimension at least two with an isomorphism
`X ∖ V ≅ Y ∖ W` over `k`. Then `ρ(X) = ρ(Y)`. -/
@[mmp "lem_mmp_projective_small_modification_picard_rank"]
public theorem picardNumber_eq_of_isoInCodimOne {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (V : Closeds X) (W : Closeds Y) (hV : 2 ≤ closedsCodimension V)
    (hW : 2 ≤ closedsCodimension W) (e : Scheme.Opens.toScheme (X := X) V.compl ≅
      Scheme.Opens.toScheme (X := Y) W.compl)
    (he : e.hom ≫ Scheme.Opens.ι (X := Y) W.compl ≫ sY = Scheme.Opens.ι (X := X) V.compl ≫ sX) :
    picardNumber sX = picardNumber sY := by
  have hXv := hX.1
  have hYv := hY.1
  have := hXv.1
  have := hYv.1
  have : IsIntegral X := hXv.1.toIsIntegral
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType sY
  have hQX := isQCartier_of_isQFactorial sX hX
  have hQY := isQCartier_of_isQFactorial sY hY
  have he' : e.symm.hom ≫ Scheme.Opens.ι (X := X) V.compl ≫ sX =
      Scheme.Opens.ι (X := Y) W.compl ≫ sY := by
    rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
  set τ := strictTransform hV hW e
  have hτ : ∀ y, τ.symm y = strictTransform hW hV e.symm y := fun y => by
    conv_lhs => rw [← strictTransform_symm_strictTransform hW hV e.symm y]
    rw [Iso.symm_symm_eq]
    exact τ.symm_apply_apply _
  have hmem : ∀ {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)}
      [QuasiCompact sZ] (hQ : ∀ G : QDivisor Z, G.IsQCartier) (G : QDivisor Z),
      G ∈ LinearMap.ker (curveIntersection sZ hQ) ↔
        ∀ C : ProperCurve sZ, G.intersectionNumber k sZ C.ι C.dim_le (hQ G) = 0 :=
    fun hQ G => by
      rw [LinearMap.mem_ker, funext_iff]
      rfl
  have hker : (LinearMap.ker (curveIntersection sX hQX)).map (τ : QDivisor X →ₗ[ℚ] QDivisor Y) =
      LinearMap.ker (curveIntersection sY hQY) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext y
    rw [Submodule.mem_comap, hmem, hmem]
    refine ⟨fun h C => ?_, fun h C => ?_⟩
    · have := intersectionNumber_strictTransform_eq_zero hX hXp hY hYp hV hW e he (τ.symm y) h C
      rwa [LinearEquiv.apply_symm_apply] at this
    · rw [LinearEquiv.coe_coe, hτ]
      exact intersectionNumber_strictTransform_eq_zero hY hYp hX hXp hW hV e.symm he' y h C
  rw [picardNumber_eq_toENat_rank sX hQX, picardNumber_eq_toENat_rank sY hQY]
  congr 1
  exact (((LinearMap.quotKerEquivRange _).symm.trans
    (Submodule.Quotient.equiv _ _ τ hker)).trans (LinearMap.quotKerEquivRange _)).rank_eq

end MMP.Fourfold
