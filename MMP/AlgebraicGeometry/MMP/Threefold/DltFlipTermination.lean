module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.Flip.NegativeAdjointTransfer
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.SpecialTermination
import MMP.AlgebraicGeometry.MMP.Threefold.KltFlipTermination

/-!
# Termination of projective dlt flips of threefolds

Let `X` be a normal projective `ℚ`-factorial complex threefold with canonical divisor `K`, and
let `B` be an effective `ℚ`-divisor such that `(X, B)` is dlt. Every sequence of flips for
`(X, B)` whose models `X_i` and contraction targets `Z_i` are all projective is finite.

## Main results

* `MMP.Fourfold.SequenceOfFlips.terminates_of_isDltPair`: projective dlt flips of threefolds
  terminate.

## Implementation notes

A sequence of flips is `MMP.Flips.SequenceOfFlips sX 3 K B`: each step is a small
`(K_{X_i} + B_i)`-negative extremal contraction followed by its flip, and `B_{i+1}` is the
transform of `B_i`. The dlt condition is `MMP.Intersection.IsDltPair` (Kollár–Mori 2.37). The
hypotheses are those of `MMP.Fourfold.ProjectiveKltTerminationLevel`, with klt replaced by dlt
and without a condition on the number `e(X, B)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_thm_mmp_projective_threefold_dlt_flip_termination

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Steps of a sequence of flips -/

section Sequence

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}

/-- In a sequence of flips of infinite length starting at an `n`-fold, every model is an
`n`-fold. -/
private theorem topologicalKrullDim_model (S : SequenceOfFlips sX n K B)
    (hlt : ∀ m : ℕ, (m : ℕ∞) < S.length) (hX : topologicalKrullDim X = n) (i : ℕ) :
    topologicalKrullDim (S.model i).1 = n := by
  induction i with
  | zero => exact (congrArg Sigma.fst S.model_zero).symm ▸ hX
  | succ i ih =>
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    rw [(S.isFlip i (hlt _)).isSmall.dim_eq, ← (S.isSmall i (hlt _)).dim_eq, ih]

section Ample

open CategoryTheory.Limits RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- If `(a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{0}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.lift a b h) (pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g (pullback.lift a b h) L N
  simp only [pullback.lift_fst, pullback.lift_snd] at e
  rw [← Category.assoc, pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_of_isRelativelyAmple {X S : Scheme.{0}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample. -/
private theorem isRelativelyAmple_add {S X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI : IsAffineHom (pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (stacks_of_isRelativelyAmple f _ hAf) (stacks_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- Every positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_zsmul {S X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) : (((n : ℤ) + 1) • L).IsRelativelyAmple f (hL.zsmul _) := by
  induction n with
  | zero => simpa using hLf
  | succ n ih =>
    convert isRelativelyAmple_add _ ih _ hLf using 2
    push_cast
    rw [add_smul, one_smul]

/-- An `f`-ample Cartier divisor in the sense of `MMP.Flips` (ample over every affine open of
the target) is `f`-ample in the sense of `MMP.Mori`. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {S X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} {L : Divisor X}
    (h : MMP.Flips.IsRelativelyAmpleCartier f L) : ∃ hL : L.IsCartier, L.IsRelativelyAmple f hL := by
  obtain ⟨hL, hamp⟩ := h
  refine ⟨hL, fun y => ?_⟩
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show y ∈ (⊤ : S.Opens) from trivial)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- A positive integral combination of `f`-ample Cartier divisors is an `f`-ample Cartier
divisor. -/
private theorem isRelativelyAmple_sum {S X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (n : ι → ℕ)
    (L : ι → Divisor X) (hL : ∀ i ∈ s, ∃ h : (L i).IsCartier, (L i).IsRelativelyAmple f h) :
    ∃ h : (∑ i ∈ s, ((n i : ℤ) + 1) • L i).IsCartier,
      (∑ i ∈ s, ((n i : ℤ) + 1) • L i).IsRelativelyAmple f h := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    obtain ⟨h, ha⟩ := hL a (Finset.mem_singleton_self a)
    rw [Finset.sum_singleton]
    exact ⟨h.zsmul _, isRelativelyAmple_zsmul h ha (n a)⟩
  | cons a s ha hs ih =>
    obtain ⟨h, h'⟩ := hL a (Finset.mem_cons_self a s)
    obtain ⟨hs', hs''⟩ := ih fun i hi => hL i (Finset.mem_cons_of_mem hi)
    rw [Finset.sum_cons]
    exact ⟨(h.zsmul _).add hs', isRelativelyAmple_add _ (isRelativelyAmple_zsmul h h' (n a)) _ hs''⟩

/-- **A positive real solution of a rational linear system gives a positive rational one.** -/
private theorem exists_pos_rat_solution {m : ℕ} {ι : Type*} (r : Fin m → ℝ) (hr : ∀ j, 0 < r j)
    (a : ι → Fin m → ℚ) (d : ι → ℚ) (h : ∀ P, ∑ j, r j * (a P j : ℝ) = (d P : ℝ)) :
    ∃ q : Fin m → ℚ, (∀ j, 0 < q j) ∧ ∀ P, ∑ j, q j * a P j = d P := by
  classical
  let u : Option (Fin m) → ℝ := fun o => o.elim 1 r
  have hu : ∀ o, 0 < u o := fun o => by cases o <;> simp [u, hr]
  let W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range u)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  let b := Module.finBasis ℚ W
  let w : Option (Fin m) → W := fun o => ⟨u o, Submodule.subset_span ⟨o, rfl⟩⟩
  have hsum : ∀ x : W, (x : ℝ) = ∑ k, (b.repr x k : ℝ) * (b k : ℝ) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Rat.smul_def]
  let C : ℝ := ∑ o, ∑ k, |(b.repr (w o) k : ℝ)|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨o₀, -, ho₀⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  set μ := u o₀
  have hμ : 0 < μ := hu o₀
  set ε : ℝ := μ / (2 * (C + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hs : ∀ k, ∃ t : ℚ, |(t : ℝ) - (b k : ℝ)| < ε := fun k => by
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show (b k : ℝ) - ε < b k + ε by linarith)
    exact ⟨t, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  choose s hs using hs
  let π : W →ₗ[ℚ] ℚ := ∑ k, s k • b.coord k
  have hπ : ∀ x : W, π x = ∑ k, b.repr x k * s k := by
    intro x; simp [π, mul_comm]
  have hest : ∀ o, μ / 2 < (π (w o) : ℝ) := by
    intro o
    have h1 : (π (w o) : ℝ) - u o = ∑ k, (b.repr (w o) k : ℝ) * ((s k : ℝ) - (b k : ℝ)) := by
      rw [hπ, show u o = ((w o : W) : ℝ) from rfl, hsum (w o)]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : |(π (w o) : ℝ) - u o| ≤ C * ε := by
      rw [h1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |(b.repr (w o) k : ℝ) * ((s k : ℝ) - (b k : ℝ))|
          ≤ ∑ k, |(b.repr (w o) k : ℝ)| * ε := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hs k).le (abs_nonneg _)
        _ = (∑ k, |(b.repr (w o) k : ℝ)|) * ε := by rw [Finset.sum_mul]
        _ ≤ C * ε := mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun o => ∑ k, |(b.repr (w o) k : ℝ)|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ o)) hεpos.le
    have h3 : C * ε < μ / 2 := by
      rw [hε]
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h4 : μ ≤ u o := ho₀ o (Finset.mem_univ _)
    have := (abs_sub_lt_iff.1 (lt_of_le_of_lt h2 h3)).2
    linarith
  have hpos : ∀ o, 0 < π (w o) := fun o => by
    have := hest o; exact_mod_cast (show (0 : ℝ) < π (w o) by linarith)
  refine ⟨fun j => π (w (some j)) / π (w none), fun j => div_pos (hpos _) (hpos _), fun P => ?_⟩
  have hW : ∑ j, a P j • w (some j) = d P • w none := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    simp only [Submodule.coe_smul, Rat.smul_def, w, u, Option.elim]
    rw [mul_one, ← h P]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hπW := congrArg π hW
  rw [map_sum, map_smul] at hπW
  simp only [map_smul, smul_eq_mul] at hπW
  have hne : π (w none) ≠ 0 := (hpos none).ne'
  have e : ∑ j, (fun j ↦ π (w (some j)) / π (w none)) j * a P j =
      (∑ j, a P j * π (w (some j))) / π (w none) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, hπW, mul_div_cancel_right₀ _ hne]

/-- A positive rational number has a positive integral multiple by a common multiple of the
denominators. -/
private theorem exists_nat_add_one_eq_mul {q : ℚ} (hq : 0 < q) {N : ℕ} (hN0 : 0 < N)
    (hN : q.den ∣ N) : ∃ k : ℕ, ((k : ℚ) + 1) = N * q := by
  obtain ⟨c, rfl⟩ := hN
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hval : ((q.den * c : ℕ) : ℚ) * q = ((c * q.num : ℤ) : ℚ) := by
    push_cast
    rw [mul_comm (q.den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hN0)
  have hpos : 1 ≤ c * q.num := by nlinarith
  refine ⟨(c * q.num).toNat - 1, ?_⟩
  rw [hval]
  have : (((c * q.num).toNat - 1 : ℕ) : ℤ) + 1 = c * q.num := by
    rw [Nat.cast_sub (by omega), Int.toNat_of_nonneg (by omega)]; push_cast; ring
  exact_mod_cast this

/-- **An `f`-ample `ℚ`-divisor has an `f`-ample Cartier multiple.** If the `ℝ`-divisor of a
`ℚ`-divisor `D` is a positive real combination of `f`-ample Cartier divisors, it is also a
positive rational combination of them, and clearing denominators gives a multiple `N D` which is
a positive integral combination of them, hence `f`-ample. -/
private theorem hasRelativelyAmpleMultiple_of_isRelativelyAmple {S X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {D : QDivisor X}
    (h : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D)) :
    D.HasRelativelyAmpleMultiple f := by
  classical
  obtain ⟨m, r, L, hm, hr, hL, hD⟩ := h
  have hcoef : ∀ P, ∑ j, r j * (((L j).coeff P : ℚ) : ℝ) = ((D.coeff P : ℚ) : ℝ) := by
    intro P
    have := congrArg (fun E : RDivisor X => E P) hD
    change ((D P : ℚ) : ℝ) = _ at this
    rw [show ((D.coeff P : ℚ) : ℝ) = ((D P : ℚ) : ℝ) from rfl, this, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    change r j * (((L j P : ℤ) : ℚ) : ℝ) = r j * (((L j P : ℤ)) : ℝ)
    push_cast; rfl
  obtain ⟨q, hq, hqeq⟩ := exists_pos_rat_solution r hr (fun P j => ((L j).coeff P : ℚ))
    (fun P => D.coeff P) hcoef
  set N : ℕ := ∏ j, (q j).den
  have hN : 0 < N := Finset.prod_pos fun j _ => (q j).den_pos
  have hint := fun j => exists_nat_add_one_eq_mul (hq j) hN
    (Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ j))
  choose n hn using hint
  obtain ⟨hL'c, hL'a⟩ := isRelativelyAmple_sum Finset.univ ⟨⟨0, hm⟩, Finset.mem_univ _⟩ n L
    (fun j _ => isRelativelyAmple_of_isRelativelyAmpleCartier (hL j))
  refine ⟨N, hN, _, hL'c, ?_, hL'a⟩
  refine Finsupp.ext fun P => ?_
  change (((∑ j, ((n j : ℤ) + 1) • L j) P : ℤ) : ℚ) = ((N : ℤ) : ℚ) * D P
  rw [Finsupp.finset_sum_apply]
  push_cast
  have h1 := hqeq P
  change ∑ j, q j * ((L j P : ℤ) : ℚ) = D P at h1
  rw [← h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [hn j]; ring

end Ample

/-- **The birational transform under a modification of small contractions, coefficientwise.**
For small contractions `φ : X ⟶ Z`, `φ⁺ : X' ⟶ Z` of normal varieties and `θ : X ⤏ X'` over `Z`,
if `φ⁺` sends the generic point of `P'` to that of `Q`, the coefficient of `P'` in `θ_* A` is the
coefficient of `Q` in `φ_* A`, for divisors `A` with coefficients in any additive monoid. -/
private theorem transformDivisor_apply_of_isOver {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian X'] [IsNormal X'] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {φ : X ⟶ Z} {φp : X' ⟶ Z} (hφ : IsSmall k sZ sX φ) (hφp : IsSmall k sZ sX' φp)
    {θ : X.RationalMap X'} (hθ : θ.compHom φp = φ.toRationalMap)
    {P' : AlgebraicGeometry.PrimeDivisor X'} {Q : AlgebraicGeometry.PrimeDivisor Z}
    (hQ : φp P'.genericPoint = Q.genericPoint) {R : Type} [AddCommMonoid R]
    (A : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor θ A P' =
      MMP.Mori.RationalMap.transformDivisor (X := X) φ.toRationalMap A Q := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'
  have : IsProper φ := hφ.isProper
  have : IsProper φp := hφp.isProper
  have hYφ : IsNormalVariety k (φ ≫ sZ) := by rw [hφ.comp_eq]; exact hX
  have hYφp : IsNormalVariety k (φp ≫ sZ) := by rw [hφp.comp_eq]; exact hX'
  have hbφ := hφ.isBirationalMorphism
  have hbφp := hφp.isBirationalMorphism
  obtain ⟨Wφ, hWφ, hWφD, -⟩ := exists_isIso_morphismRestrict_of_isSmall hφ
  obtain ⟨Wp, hWp, -, hWpQ⟩ := exists_isIso_morphismRestrict_of_isSmall hφp
  obtain ⟨E, hEQ, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hYφ hbφ Q
  have hd : Dense ((φ ⁻¹ᵁ Wp : X.Opens) : Set X) :=
    (φ ⁻¹ᵁ Wp).isOpen.dense ⟨E.genericPoint, show φ E.genericPoint ∈ Wp from hEQ ▸ hWpQ Q⟩
  let g' : X.PartialMap X' := Scheme.PartialMap.mk (φ ⁻¹ᵁ Wp) hd
    ((φ ∣_ Wp ≫ inv (φp ∣_ Wp)) ≫ (φp ⁻¹ᵁ Wp).ι)
  have hg' : g'.toRationalMap = θ :=
    toRationalMap_eq_of_comp_morphismRestrict_eq hd (by simp) hθ
  have key : g'.hom ≫ φp = (φ ⁻¹ᵁ Wp).ι ≫ φ := by
    change ((φ ∣_ Wp ≫ inv (φp ∣_ Wp)) ≫ (φp ⁻¹ᵁ Wp).ι) ≫ φp = _
    simp only [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hcomp : ∀ x : (φ ⁻¹ᵁ Wp).toScheme, φp (g'.hom x) = φ x.1 := fun x =>
    congrArg (fun g : (φ ⁻¹ᵁ Wp).toScheme ⟶ Z ↦ g x) key
  have hD : ∀ D : AlgebraicGeometry.PrimeDivisor X, ∃ Q' : AlgebraicGeometry.PrimeDivisor Z,
      φ D.genericPoint = Q'.genericPoint ∧ ∃ P'' : AlgebraicGeometry.PrimeDivisor X',
        MMP.Mori.RationalMap.transformPrimeDivisor θ D = some P'' ∧
          φp P''.genericPoint = Q'.genericPoint := by
    intro D
    obtain ⟨Q', hQ'⟩ := exists_primeDivisor_map_genericPoint_eq φ Wφ D (hWφD D)
    have hDU : D.genericPoint ∈ g'.domain :=
      show φ D.genericPoint ∈ Wp from hQ' ▸ hWpQ Q'
    have hy : φp (g'.hom ⟨D.genericPoint, hDU⟩) = Q'.genericPoint := (hcomp _).trans hQ'
    have hcy : Order.coheight (g'.hom ⟨D.genericPoint, hDU⟩) = 1 := by
      rw [← coheight_map_eq_of_isIso_morphismRestrict φp Wp
        (show φp (g'.hom ⟨D.genericPoint, hDU⟩) ∈ Wp from hy ▸ hWpQ Q'), hy,
        Q'.coheight_genericPoint]
    refine ⟨Q', hQ', .ofCoheightOne _ hcy, transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg'
      hDU (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy), ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hy
  obtain ⟨Q₁, hQ₁, P'', hP'', hP''Q₁⟩ := hD E
  have hQ₁Q : Q₁ = Q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hQ₁.symm.trans hEQ)
  rw [hQ₁Q] at hP''Q₁
  have hPP : P'' = P' := by
    have h1 := transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hbφp hP''Q₁
      (Finsupp.single P' (1 : ℤ))
    rw [transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hbφp hQ, Finsupp.single_eq_same,
      Finsupp.single_apply] at h1
    split_ifs at h1 with h
    · exact h.symm
    · exact absurd h1 one_ne_zero
  rw [hPP] at hP''
  rw [hE A]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP'' (fun D' hD' => ?_) A
  obtain ⟨Q', hQ', P₃, hP₃, hP₃Q⟩ := hD D'
  rw [hD'] at hP₃
  cases Option.some.inj hP₃
  have hQQ : Q' = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP₃Q.symm.trans hQ)
  rw [hQQ] at hQ'
  have h1 := transformDivisor_apply_of_map_genericPoint_eq hZ hYφ hbφ hQ'
    (Finsupp.single E (1 : ℤ))
  rw [hE, Finsupp.single_eq_same, Finsupp.single_apply] at h1
  split_ifs at h1 with h
  · exact h.symm
  · exact absurd h1 one_ne_zero

/-- **A modification of small contractions transforms divisors as `(φ⁺)⁻¹_* φ_*`.** -/
private theorem transformDivisor_eq_flipTransform_of_isSmall {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian X'] [IsNormal X'] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {φ : X ⟶ Z} {φp : X' ⟶ Z} (hφ : IsSmall k sZ sX φ) (hφp : IsSmall k sZ sX' φp)
    {θ : X.RationalMap X'} (hθ : θ.compHom φp = φ.toRationalMap) {R : Type} [AddCommMonoid R]
    (A : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor θ A = flipTransform φ φp A := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨W, hW, -, hWQ⟩ := exists_isIso_morphismRestrict_of_isSmall hφp
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hφp P'
  rw [transformDivisor_apply_of_isOver hZ hX hX' hφ hφp hθ hQ A]
  have hV : φp P'.genericPoint ∈ biregularLocus φp :=
    le_biregularLocus (f := φp) hW (hQ ▸ hWQ Q)
  change _ = DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor φp)
    (MMP.Mori.RationalMap.transformDivisor (X := X) φ.toRationalMap A) P'
  exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ hV)
    (fun Q' hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hQ) _).symm

/-- The boundary of the next model is the transform `(φ_i⁺)⁻¹_* (φ_i)_* B_i`. -/
private theorem model_boundary_eq_flipTransform (S : SequenceOfFlips sX n K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    (S.model (i + 1)).2.2.2 = flipTransform (S.contraction i) (S.flip i) (S.model i).2.2.2 := by
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  have hE := S.isNegativeExtremalContraction i hi
  have hZ := hE.isNormalVariety_target
  haveI : IsNormal (S.base i) := hZ.2
  haveI : LocallyOfFiniteType (S.baseStr i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (S.base i) := LocallyOfFiniteType.isLocallyNoetherian (S.baseStr i)
  have hF := S.isFlip i hi
  rw [S.transform_eq i hi]
  exact transformDivisor_eq_flipTransform_of_isSmall hZ hE.isNormalVariety_source
    hF.isNormalVariety_flip (S.isSmall i hi) hF.isSmall hF.isModificationOf.2 _

/-- A small birational contraction has exceptional set of codimension at least two: it is an
isomorphism over the complement of a closed subset of codimension at least two of the target, and
the preimage of that complement is the complement of a closed subset of codimension at least two of
the source. -/
private theorem two_le_closedsCodimension_exceptionalSet_of_isSmall {k : Type} [Field k]
    {Y Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ Z}
    (hf : IsSmall k sZ sY f) : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f) := by
  have := hf.isVariety_source.toIsIntegral
  have := hf.isProper
  obtain ⟨V₀, W₀, hV₀, -, h₀, hiso⟩ := hf.exists_isIso
  have hle := preimage_le_of_isIso_resLE f V₀.compl W₀.compl h₀
    (nonempty_compl_of_two_le_closedsCodimension V₀ hV₀)
  have key : ∀ (U : Y.Opens) (hU : U = f ⁻¹ᵁ W₀.compl) (h : U ≤ f ⁻¹ᵁ W₀.compl),
      IsIso (f.resLE W₀.compl U h) → IsIso (f ∣_ W₀.compl) := by
    rintro _ rfl h hi
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  have hbir : W₀.compl ≤ MMP.Mori.biregularLocus f :=
    MMP.Mori.le_biregularLocus (key _ (le_antisymm h₀ hle) h₀ hiso)
  refine MMP.Mori.le_closedsCodimension_iff.2 fun W hW =>
    MMP.Mori.le_closedsCodimension_iff.1 hV₀ W (hW.trans ?_)
  intro y hy
  by_contra hyV
  exact hy (hbir (h₀ hyV))

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsProper f]
    [IsDominant f] : Function.Surjective f := by
  rw [← Set.range_eq_univ, ← f.isClosedMap.isClosed_range.closure_eq]
  exact f.denseRange.closure_range

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {Y Y' : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S]
    (φ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor Y')) (f : R →+ S)
    (D : DivisorWithCoeffs R Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The log canonical `ℝ`-divisor of a `ℚ`-boundary is the `ℝ`-divisor of the `ℚ`-divisor
`K + D`. -/
private theorem logCanonicalDivisor_toRDivisor {Y : Scheme.{0}} (KY : Divisor Y) (D : QDivisor Y) :
    logCanonicalDivisor KY (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (Divisor.toQDivisor KY + D) := by
  rw [logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- Each step of a sequence of flips with projective contraction targets is a flip in the sense
of `MMP.Fourfold.IsFlipOf`: the `ℝ`-ampleness of the steps is `ℚ`-ampleness for the rational
divisor `K_i + B_i`, and relative ampleness over a projective target makes both contractions
projective. -/
private theorem isFlipOf_step (S : SequenceOfFlips sX n K B)
    {i : ℕ} (hX : MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ (S.model (i + 1)).2.1)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    IsFlipOf (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
      (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) (S.contraction i) (S.flip i) := by
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  have hE := S.isNegativeExtremalContraction i hi
  have hF := S.isFlip i hi
  have hs := S.isSmall i hi
  have hs' := hF.isSmall
  have hZ := hE.isNormalVariety_target
  haveI : IsNormal (S.base i) := hZ.2
  haveI : LocallyOfFiniteType (S.baseStr i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (S.base i) := LocallyOfFiniteType.isLocallyNoetherian (S.baseStr i)
  haveI : IsSeparated (S.baseStr i) := hZp.toIsSeparated
  haveI : IsProper (S.contraction i) := hs.isProper
  haveI : IsProper (S.flip i) := hF.isProper
  haveI : LocallyOfFiniteType (S.model i).2.1 := hE.isNormalVariety_source.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (S.model (i + 1)).2.1 :=
    hF.isNormalVariety_flip.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (S.contraction i ≫ S.baseStr i) := hs.comp_eq ▸ inferInstance
  haveI : LocallyOfFiniteType (S.contraction i) :=
    LocallyOfFiniteType.of_comp (g := S.baseStr i) inferInstance
  haveI : LocallyOfFiniteType (S.flip i ≫ S.baseStr i) := hs'.comp_eq ▸ inferInstance
  haveI : LocallyOfFiniteType (S.flip i) := LocallyOfFiniteType.of_comp (g := S.baseStr i) inferInstance
  have hb := hs.isBirationalMorphism
  haveI : IsIntegral (S.model i).1 := hE.isNormalVariety_source.1.toIsIntegral
  haveI : IsDominant (S.contraction i) := hb.isDominant
  have heq := logCanonicalDivisor_toRDivisor (S.model i).2.2.1 (S.model i).2.2.2
  have htr : MMP.Mori.RationalMap.transformDivisor (S.flipMap i)
      (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2)) =
        QDivisor.toRDivisor (flipTransform (S.contraction i) (S.flip i)
          (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2)) := by
    rw [heq, ← transformDivisor_eq_flipTransform_of_isSmall hZ hE.isNormalVariety_source
      hF.isNormalVariety_flip hs hs' hF.isModificationOf.2]
    exact mapPrimeDivisors_mapCoeffsAddMonoidHom _ _ _
  exact
    { isQCartier := QDivisor.isQCartier_of_isCartierCombination (heq ▸ hE.isCartierCombination)
      isContraction :=
        { isNormalVariety_source := hE.isNormalVariety_source
          isNormalVariety_target := hZ
          comp_eq := hs.comp_eq
          isProjectiveMorphism := IsProjectiveMorphism.of_comp _ (S.baseStr i)
            (by rw [hs.comp_eq]; exact hX.isProjective)
          surjective := surjective_of_isProper_of_isDominant _
          isIso_app := hE.isContraction.isIso_app }
      isSmallMorphism := ⟨hE.isNormalVariety_source, hZ, hs.comp_eq, inferInstance, hb,
        two_le_closedsCodimension_exceptionalSet_of_isSmall hs⟩
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_of_isRelativelyAmple
        (by rw [map_neg, ← heq]; exact hE.isRelativelyAntiAmple)
      isSmallMorphism_flip := ⟨hF.isNormalVariety_flip, hZ, hs'.comp_eq, inferInstance,
        hs'.isBirationalMorphism, two_le_closedsCodimension_exceptionalSet_of_isSmall hs'⟩
      isProjectiveMorphism_flip := IsProjectiveMorphism.of_comp _ (S.baseStr i)
        (by rw [hs'.comp_eq]; exact hX'.isProjective)
      isQCartier_flip := QDivisor.isQCartier_of_isCartierCombination
        (htr ▸ hF.isCartierCombination_transform)
      hasRelativelyAmpleMultiple_flip := hasRelativelyAmpleMultiple_of_isRelativelyAmple
        (htr ▸ hF.isRelativelyAmple_transform) }

/-! ### Points over an open on which a morphism is an isomorphism -/

section IsoOver

variable {Y Z : Scheme.{0}} (f : Y ⟶ Z) (W : Z.Opens) [IsIso (f ∣_ W)]

/-- Over an open `W` on which `f` is an isomorphism, every point of `W` has a preimage. -/
private theorem exists_apply_eq_of_isIso_morphismRestrict {z : Z} (hz : z ∈ W) :
    ∃ y : Y, f y = z := by
  refine ⟨((inv (f ∣_ W)) ⟨z, hz⟩ : (f ⁻¹ᵁ W).toScheme).1, ?_⟩
  exact congrArg (fun g : W.toScheme ⟶ Z => g ⟨z, hz⟩)
    (show inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι ≫ f = W.ι by
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc])

/-- Over an open `W` on which `f` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq_of_isIso_morphismRestrict {y y' : Y} (hy : f y ∈ W)
    (h : f y = f y') : y = y' := by
  have hy' : f y' ∈ W := h ▸ hy
  have := (f ∣_ W).isOpenEmbedding.injective (a₁ := ⟨y, hy⟩) (a₂ := ⟨y', hy'⟩) (Subtype.ext (by
    change ((f ∣_ W) ≫ W.ι) ⟨y, hy⟩ = ((f ∣_ W) ≫ W.ι) ⟨y', hy'⟩
    rw [morphismRestrict_ι]; exact h))
  exact congrArg Subtype.val this

end IsoOver

/-- For small contractions `f : X ⟶ Z` and `f⁺ : X⁺ ⟶ Z`, every prime divisor `P` of `X` has a
prime divisor `P⁺` of `X⁺` over the same point of `Z`. -/
private theorem exists_primeDivisor_map_genericPoint_eq_of_isSmall' {k : Type} [Field k]
    {X X' Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ Z} {fp : X' ⟶ Z} (hs : IsSmall k sZ sX f)
    (hs' : IsSmall k sZ sX' fp) (P : AlgebraicGeometry.PrimeDivisor X) :
    ∃ P' : AlgebraicGeometry.PrimeDivisor X', f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hs P
  obtain ⟨W, hW, -, hWQ⟩ := exists_isIso_morphismRestrict_of_isSmall hs'
  obtain ⟨p', hp'⟩ := exists_apply_eq_of_isIso_morphismRestrict fp W (hWQ Q)
  have hcoh : Order.coheight p' = 1 := by
    rw [← coheight_map_eq_of_isIso_morphismRestrict fp W (hp' ▸ hWQ Q), hp',
      Q.coheight_genericPoint]
  exact ⟨.ofCoheightOne p' hcoh, by
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hp', hQ]⟩

/-- **The strict transform under small contractions, coefficientwise.** If `f` and `f⁺` are
small contractions of normal varieties and `f(η_P) = f⁺(η_{P⁺})`, then the coefficient of `P⁺` in
`(f⁺)⁻¹_* f_* D` is the coefficient of `P` in `D`. -/
private theorem flipTransform_apply_of_isSmall {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hs : IsSmall k sZ sX f) (hs' : IsSmall k sZ sX' fp)
    {P : AlgebraicGeometry.PrimeDivisor X} {P' : AlgebraicGeometry.PrimeDivisor X'}
    (h : f P.genericPoint = fp P'.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  have : IsProper f := hs.isProper
  have hYf : IsNormalVariety k (f ≫ sZ) := by rw [hs.comp_eq]; exact hX
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hs P
  obtain ⟨W, hW, -, hWQ⟩ := exists_isIso_morphismRestrict_of_isSmall hs'
  obtain ⟨Wf, hWf, hWfD, -⟩ := exists_isIso_morphismRestrict_of_isSmall hs
  have hQ' : fp P'.genericPoint = Q.genericPoint := h.symm.trans hQ
  have hV : fp P'.genericPoint ∈ biregularLocus fp := le_biregularLocus (f := fp) hW (hQ' ▸ hWQ Q)
  change DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor fp)
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) P' = D P
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ' hV)
    (fun Q' hQ'' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ'').1.symm.trans hQ')]
  obtain ⟨E, hEQ, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hYf
      hs.isBirationalMorphism Q
  rw [hE D]
  have hEP : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
    eq_of_apply_eq_of_isIso_morphismRestrict f Wf (hWfD E) (hEQ.trans hQ.symm)
  rw [hEP]

end Sequence

/-- **The strict transform under small contractions commutes with changing coefficients.** For
small contractions `f`, `f⁺` of normal varieties, `(f⁺)⁻¹_* f_*` acts on coefficients through a
bijection of prime divisors, so it commutes with every coefficient map `φ` with `φ 0 = 0`. -/
private theorem flipTransform_mapCoeffs {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hs : IsSmall k sZ sX f) (hs' : IsSmall k sZ sX' fp)
    {R S : Type} [AddCommMonoid R] [AddCommMonoid S] (φ : R → S) (h0 : φ 0 = 0)
    (D : DivisorWithCoeffs R X) :
    flipTransform f fp (D.mapCoeffs φ h0) = (flipTransform f fp D).mapCoeffs φ h0 := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall' hs' hs P'
  have h1 := flipTransform_apply_of_isSmall hZ hX hs hs' hP.symm (D.mapCoeffs φ h0)
  have h2 := flipTransform_apply_of_isSmall hZ hX hs hs' hP.symm D
  change _ = φ (flipTransform f fp D P')
  rw [h1, h2]
  rfl

/-- An `f`-ample `ℚ`-divisor in the sense of `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple` is
`f`-ample as an `ℝ`-divisor: it is `1 / m` times an `f`-ample Cartier divisor. -/
private theorem isRelativelyAmple_of_hasRelativelyAmpleMultiple {Y W : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ W} [QuasiCompact f]
    {D : QDivisor Y} (h : D.HasRelativelyAmpleMultiple f) :
    MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => isRelativelyAmpleCartier_of_isRelativelyAmple hL hamp, ?_⟩
  rw [Fin.sum_univ_one]
  exact MMP.Mori.QDivisor.toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] {D : QDivisor Y} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact MMP.Mori.QDivisor.toRDivisor_eq_inv_smul hm hL⟩

/-! ### Relative cones in relative Picard number one -/

/-- The natural map `N₁(X/Y) → N₁(X)` is injective: a relative 1-cycle numerically trivial on
`X` is relatively numerically trivial, by definition. -/
private theorem relativeToAbsolute_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k))
    (f : X ⟶ Y) : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.mem_ker, isNaturalRelativeMap_relativeToAbsolute sX f Z] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)

/-- **`ρ(X/Z) = 1` makes `N₁(X/Z)` at most a line.** The pairing embeds `N₁(X/Z)` into the
annihilator of the numerically `f`-trivial divisors, the dual of the line `N¹(X/Z)`; so every
class is a multiple of a nonzero one. -/
private theorem exists_smul_eq_of_relativePicardNumber_eq_one {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {v : RelativeNumericalCurveClasses sX f} (hv : v ≠ 0) (z : RelativeNumericalCurveClasses sX f) :
    ∃ c : ℝ, c • v = z := by
  set W := MMP.Flips.relativeNumericallyTrivialDivisors sX f
  have hrank : Module.finrank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
    have h1 : Module.rank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
      unfold MMP.Flips.relativePicardNumber at hρ
      exact Cardinal.toENat_eq_one.mp hρ
    exact Module.finrank_eq_of_rank_eq (by rw [h1]; simp)
  have : FiniteDimensional ℝ (KCartierDivisor ℝ X ⧸ W) :=
    Module.finite_of_finrank_eq_succ hrank
  have hann : ∀ (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X), D ∈ W →
      curvePairing sX (relativeToAbsolute sX f z) D = 0 := by
    intro z D hD
    obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
    rw [isNaturalRelativeMap_relativeToAbsolute sX f]
    change OneCycle.intersectionPairing D Z = 0
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors] at hD
    rw [relativeOneCycles, Finsupp.mem_supported] at hZ
    rw [← Finsupp.sum_single Z, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun C hC => ?_
    have hs : Finsupp.single C (Z C) = Z C • C.cycle ℝ := by
      rw [ProperCurve.cycle, Finsupp.smul_single_one]
    rw [hs, map_smul]
    rw [show OneCycle.intersectionPairing D (C.cycle ℝ) = 0 from hD C (hZ hC), smul_zero]
  let φ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] W.dualAnnihilator :=
    LinearMap.codRestrict W.dualAnnihilator (curvePairing sX ∘ₗ relativeToAbsolute sX f)
      fun z => (Submodule.mem_dualAnnihilator _).mpr fun D hD => hann z D hD
  let ψ := W.dualQuotEquivDualAnnihilator.symm.toLinearMap ∘ₗ φ
  have hψ : Function.Injective ψ := by
    intro z₁ z₂ h
    have h1 : φ z₁ = φ z₂ := W.dualQuotEquivDualAnnihilator.symm.injective h
    have h2 : curvePairing sX (relativeToAbsolute sX f z₁) =
        curvePairing sX (relativeToAbsolute sX f z₂) := congrArg Subtype.val h1
    refine relativeToAbsolute_injective sX f (numericalPairing_flip_injective sX ?_)
    refine LinearMap.ext fun d => ?_
    obtain ⟨D, rfl⟩ := (numericallyTrivialDivisors sX).mkQ_surjective d
    exact LinearMap.congr_fun h2 D
  have hfin : Module.finrank ℝ (Module.Dual ℝ (KCartierDivisor ℝ X ⧸ W)) = 1 := by
    rw [Subspace.dual_finrank_eq, hrank]
  have := Module.Finite.of_injective ψ hψ
  have hle : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) ≤ 1 :=
    hfin ▸ LinearMap.finrank_le_finrank_of_injective hψ
  have h1 : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) = 1 :=
    le_antisymm hle (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩)
  exact (finrank_eq_one_iff_of_nonzero' v hv).mp h1 z

/-- A continuous linear form on `N₁(X/S)` which is nonnegative on the class of every curve
contracted by `g` is nonnegative on `NE̅(X/S)`. -/
private theorem nonneg_of_mem_relativeClosedConeOfCurves {k : Type} [Field k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {g : X ⟶ S}
    (φ : RelativeNumericalCurveClasses sX g →ₗ[ℝ] ℝ) (hφc : Continuous φ)
    (hφ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), 0 ≤ φ (C.relativeClass g hC))
    {z : RelativeNumericalCurveClasses sX g}
    (hz : z ∈ (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g))) :
    0 ≤ φ z := by
  have hcone : (relativeConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) ⊆
      {w | 0 ≤ φ w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hφ C hC
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      linarith
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  rw [coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hcone (isClosed_le continuous_const hφc) hz

/-! ### The lowered boundary -/

/-- The lowered boundary `B - ½ ⌊B⌋`, coefficientwise `b ↦ b - ⌊b⌋ / 2`. -/
private noncomputable def lowerBoundary {Y : Scheme.{0}} (D : QDivisor Y) : QDivisor Y :=
  D.mapCoeffs (fun q : ℚ => q - (⌊q⌋ : ℚ) / 2) (by simp)

private theorem coeff_lowerBoundary {Y : Scheme.{0}} (D : QDivisor Y) (P : MMP.Mori.PrimeDivisor Y) :
    (lowerBoundary D).coeff P = D.coeff P - (⌊D.coeff P⌋ : ℚ) / 2 :=
  DivisorWithCoeffs.coeff_mapCoeffs _ _ _ _

/-- `B - ½ ⌊B⌋` as a difference of `ℚ`-divisors. -/
private theorem lowerBoundary_eq {Y : Scheme.{0}} (D : QDivisor Y) :
    lowerBoundary D = D - (1 / 2 : ℚ) • Divisor.toQDivisor D.roundDown := by
  refine Finsupp.ext fun P => ?_
  have h := coeff_lowerBoundary D P
  change (lowerBoundary D) P = D P - (1 / 2 : ℚ) * ((D.roundDown P : ℤ) : ℚ)
  change (lowerBoundary D) P = D P - (⌊D P⌋ : ℚ) / 2 at h
  rw [h, DivisorWithCoeffs.roundDown, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply]
  ring

/-- For a coefficient `0 ≤ b ≤ 1`, the lowered coefficient `b - ⌊b⌋ / 2` lies in `[0, b]` and is
less than one. -/
private theorem lowered_coeff_bounds {b : ℚ} (h0 : 0 ≤ b) (h1 : b ≤ 1) :
    0 ≤ b - (⌊b⌋ : ℚ) / 2 ∧ b - (⌊b⌋ : ℚ) / 2 ≤ b ∧ b - (⌊b⌋ : ℚ) / 2 < 1 := by
  rcases h1.lt_or_eq with h | rfl
  · rw [Int.floor_eq_zero_iff.mpr ⟨h0, h⟩]
    norm_num
    exact ⟨h0, h⟩
  · norm_num

section Lower

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}

/-- The coefficients of a dlt boundary lie in `[0, 1]`. -/
private theorem coeff_mem_Icc (hdlt : MMP.Intersection.IsDltPair sX B) (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ B.coeff P ∧ B.coeff P ≤ 1 :=
  ⟨hdlt.1.2.1 P, hdlt.2.1 P⟩

/-- Lowering the boundary of a `ℚ`-factorial dlt pair keeps it dlt. -/
private theorem isDltPair_lowerBoundary (hQ : IsQFactorial sX)
    (hdlt : MMP.Intersection.IsDltPair sX B) :
    MMP.Intersection.IsDltPair sX (lowerBoundary B) := by
  refine MMP.Intersection.IsDltPair.of_le sX hdlt (Finsupp.le_def.mpr fun P => ?_)
    (Finsupp.le_def.mpr fun P => ?_)
    (isQCartier_of_isQFactorial sX hQ _)
  · have := (lowered_coeff_bounds (coeff_mem_Icc hdlt P).1 (coeff_mem_Icc hdlt P).2).1
    rw [← coeff_lowerBoundary] at this
    exact this
  · have := (lowered_coeff_bounds (coeff_mem_Icc hdlt P).1 (coeff_mem_Icc hdlt P).2).2.1
    rw [← coeff_lowerBoundary] at this
    exact this

/-- **Lowering the reduced boundary gives a klt pair.** For `X` `ℚ`-factorial and `(X, B)` dlt,
`(X, B - ½ ⌊B⌋)` is klt: it is dlt with all coefficients less than one. -/
private theorem isKltPair_lowerBoundary (hQ : IsQFactorial sX)
    (hdlt : MMP.Intersection.IsDltPair sX B) : IsKltPair sX (lowerBoundary B) :=
  (isDltPair_lowerBoundary hQ hdlt).isKltPair_of_forall_coeff_lt_one (k := ℂ) fun P => by
    rw [coeff_lowerBoundary]
    exact (lowered_coeff_bounds (coeff_mem_Icc hdlt P).1 (coeff_mem_Icc hdlt P).2).2.2

/-- The lowered boundary is effective. -/
private theorem isEffective_lowerBoundary (hdlt : MMP.Intersection.IsDltPair sX B) :
    (lowerBoundary B).IsEffective := fun P => by
  rw [coeff_lowerBoundary]
  exact (lowered_coeff_bounds (coeff_mem_Icc hdlt P).1 (coeff_mem_Icc hdlt P).2).1

/-- The lowered boundary is klt in the sense of *Flips and abundance*. -/
private theorem isKawamataLogTerminal_lowerBoundary [LocallyOfFiniteType sX] {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 3) (hQ : IsQFactorial sX)
    (hdlt : MMP.Intersection.IsDltPair sX B) :
    IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor (lowerBoundary B)) := by
  have hklt := isKltPair_lowerBoundary hQ hdlt
  have hMori := (isKltPair_iff_mori_isKltPair sX hK hklt.1).mp hklt
  refine (isKawamataLogTerminal_iff_isKltPair sX 3 K (lowerBoundary B) hQ.1 hK (fun P => ?_)
    (isQCartier_of_isQFactorial sX hQ _)).mpr hMori
  rw [QDivisor.coeff_toRDivisor, coeff_lowerBoundary]
  have h := lowered_coeff_bounds (coeff_mem_Icc hdlt P).1 (coeff_mem_Icc hdlt P).2
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.2.le⟩

end Lower

/-- The ray `ℝ_{≥0} [C₀] ⊆ N₁(X)` spanned by the class of a proper curve. -/
private abbrev curveRay {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    (C₀ : ProperCurve sY) : Set (NumericalCurveClasses sY) :=
  {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sY (C₀.cycle ℝ) = u}

section Step

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}

/-- **The ray of a contraction of relative Picard number one.** Let `f : X ⟶ Z` be a contraction
of projective varieties with `ρ(X/Z) = 1` and `-D` `f`-ample. Then `f` contracts a proper curve
`C₀`, the ray `ℝ_{≥0} [C₀]` is a `D`-negative extremal ray of `NE̅(X)`, and `f` is its
contraction. -/
private theorem exists_curveRay (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : MMP.Fourfold.IsContraction sX sZ f)
    {D : QDivisor X} (hD : D.IsQCartier) (hamp : (-D).HasRelativelyAmpleMultiple f)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1) :
    ∃ C₀ : ProperCurve sX, C₀.IsContractedBy f ∧ IsNegativeExtremalRayOf sX D (curveRay C₀) ∧
      IsContractionOfRay sX sZ (curveRay C₀) f := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : QuasiCompact sX := hf.isNormalVariety_source.1.toQuasiCompact
  haveI : IsSeparated sZ := hf.isNormalVariety_target.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hf.isNormalVariety_target.1.toLocallyOfFiniteType
  obtain ⟨C₀, hC₀⟩ :=
    MMP.Flips.exists_properCurve_isContractedBy_of_relativePicardNumber_eq_one f hρ
  have hneg : QDivisor.curveForm sX D hD (OneCycle.numericalClass sX (C₀.cycle ℝ)) < 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact_mod_cast MMP.Fourfold.intersectionNumber_neg_of_isContractedBy hamp C₀ hC₀ hD
  -- the degree of an `f`-ample Cartier multiple of `-D` is positive on `NE(X/Z) ∖ 0`
  obtain ⟨m, hm, L, hL, -, hLa⟩ := hamp
  haveI := hL.isInvertibleModule_divisorialSheaf
  set ℓ := RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf with hℓdef
  have hℓ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), 0 < ℓ (C.relativeClass f hC) := by
    intro C hC
    have h := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
      hLa C hC
    change (0 : ℝ) < OneCycle.degree ℝ sX L.divisorialSheaf (C.cycle ℝ)
    rw [OneCycle.degree_cycle]
    exact_mod_cast h
  have hℓc : Continuous ℓ := RelativeNumericalCurveClasses.continuous_degree sX f _
  set v := C₀.relativeClass f hC₀ with hvdef
  have hv : v ≠ 0 := fun h0 => (hℓ C₀ hC₀).ne' (by rw [← hvdef, h0, map_zero])
  -- `NE̅(X/Z)` is the ray of `v`
  have hray : ∀ z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)),
      ∃ c : ℝ, 0 ≤ c ∧ c • v = z := by
    intro z hz
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_relativePicardNumber_eq_one hρ hv z
    refine ⟨c, ?_, rfl⟩
    have h1 := nonneg_of_mem_relativeClosedConeOfCurves ℓ hℓc (fun C hC => (hℓ C hC).le) hz
    rw [map_smul, smul_eq_mul] at h1
    by_contra hc
    push Not at hc
    nlinarith [hℓ C₀ hC₀]
  have hvN : v ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) := by
    rw [coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hC₀)
  have hRel : (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    ext z
    exact ⟨fun hz => hray z hz, by
      rintro ⟨c, hc, rfl⟩
      exact (relativeClosedConeOfCurves sX f).smul_mem hc hvN⟩
  have hRext : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      (relativeClosedConeOfCurves sX f) :=
    ⟨⟨subset_rfl, isCone_coe _, fun u hu w hw => (relativeClosedConeOfCurves sX f).add_mem hu hw,
      fun u hu w hw _ => ⟨hu, hw⟩⟩, v, hv, hRel⟩
  have himg : relativeToAbsolute sX f ''
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      curveRay C₀ := by
    rw [hRel]
    ext u
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul]; rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, by rw [map_smul]; rfl⟩
  have hext := isExtremalRay_image_relativeToAbsolute sX sZ f hf.comp_eq hRext
  rw [himg] at hext
  refine ⟨C₀, hC₀, ⟨hD, hext, ?_⟩, { toIsContraction := hf, isContractedBy_iff := fun C => ?_ }⟩
  · rintro u ⟨c, hc, rfl⟩ hu
    have hc0 : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact hu (zero_smul _ _))
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc0 hneg
  constructor
  · intro hC
    obtain ⟨c, hc, hcv⟩ := hray _ (by
      rw [coe_relativeClosedConeOfCurves]
      exact subset_closure (relativeClass_mem_relativeConeOfCurves hC))
    refine ⟨c, hc, ?_⟩
    have := congrArg (relativeToAbsolute sX f) hcv
    rw [map_smul] at this
    exact this
  · rintro ⟨c, hc, hcC⟩
    obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
    refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf.comp_eq H hHa C ?_
    have h1 : ((C.degree ℂ ((Scheme.Modules.pullback f).obj H) : ℤ) : ℝ) =
        c * ((C₀.degree ℂ ((Scheme.Modules.pullback f).obj H) : ℤ) : ℝ) := by
      rw [← OneCycle.degree_cycle ℝ, ← OneCycle.degree_cycle ℝ,
        ← NumericalCurveClasses.degree_numericalClass, ← NumericalCurveClasses.degree_numericalClass,
        ← hcC, map_smul, smul_eq_mul]
    rw [C₀.degree_pullback_eq_zero_of_isContractedBy f hf.comp_eq hC₀ H] at h1
    exact_mod_cast (by simpa using h1 : ((C.degree ℂ ((Scheme.Modules.pullback f).obj H) : ℤ) : ℝ) = 0)

/-- **A late step of the sequence is a flip of the lowered boundary.** Let `(X, B)` be a projective
`ℚ`-factorial dlt threefold and `f` a step of a sequence of flips, contracting the ray
`ℝ_{≥0} [C₀]`, whose exceptional set misses `⌊B⌋`. Then `C₀` misses `⌊B⌋`, so `(⌊B⌋ · C₀) = 0`
and `K + B - ½ ⌊B⌋` is negative on the ray; the flip of `K + B` is the flip of
`K + B - ½ ⌊B⌋` (`MMP.Fourfold.IsFlipOf.of_isNegativeExtremalRayOf`), and lowering the boundary
commutes with the strict transform. -/
private theorem tail_step [LocallyOfFiniteType sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX) {K : Divisor X} {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B) (hK : K.IsCanonicalDivisor sX 3)
    {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}
    (hE : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K (QDivisor.toRDivisor B)) f)
    (hs : IsSmall ℂ sZ sX f)
    (hF : MMP.Flips.IsFlip ℂ sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor B)) f fp g)
    (hFo : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) (curveRay C₀))
    (hRc : IsContractionOfRay sX sZ (curveRay C₀) f)
    (hdisj : ∀ P : MMP.Mori.PrimeDivisor X, 1 ≤ B.coeff P →
      Disjoint (P.support : Set X) (MMP.Mori.exceptionalSet f : Set X)) :
    IsNegativeExtremalContraction ℂ sX sZ
        (logCanonicalDivisor K (QDivisor.toRDivisor (lowerBoundary B))) f ∧
      MMP.Flips.IsFlip ℂ sX sZ sX'
        (logCanonicalDivisor K (QDivisor.toRDivisor (lowerBoundary B))) f fp g ∧
      lowerBoundary (RationalMap.transformDivisor g B) =
        RationalMap.transformDivisor g (lowerBoundary B) := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  have hZ := hE.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := hs.isProper
  haveI : IsProper fp := hF.isProper
  set C := lowerBoundary B with hCdef
  set F : QDivisor X := Divisor.toQDivisor B.roundDown with hFdef
  have hCF : C = B - (1 / 2 : ℚ) • F := lowerBoundary_eq B
  have hFq : F.IsQCartier := isQCartier_of_isQFactorial sX hQ F
  have hKBq : (Divisor.toQDivisor K + B).IsQCartier := hFo.isQCartier
  have hKCq : (Divisor.toQDivisor K + C).IsQCartier := isQCartier_of_isQFactorial sX hQ _
  have hsF : ((-(1 / 2) : ℚ) • F).IsQCartier := isQCartier_of_isQFactorial sX hQ _
  have hCklt : IsKltPair sX C := isKltPair_lowerBoundary hQ hdlt
  -- the curve `C₀` lies in `Ex(f)`, which misses `⌊B⌋`
  have hcon := hRc.toIsContraction
  have hsub : closure ({C₀.point} : Set X) ⊆ (MMP.Mori.exceptionalSet f : Set X) := by
    refine MMP.Mori.subset_exceptionalSet_of_subsingleton_image hcon.isNormalVariety_source.1
      hcon.isNormalVariety_target.1 hcon.comp_eq hFo.isSmallMorphism.isBirationalMorphism
      isClosed_closure isIrreducible_singleton.closure ?_ ?_
    · exact (MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq C₀.point).symm.trans C₀.dim_eq
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hC₀ x hx).trans (hC₀ y hy).symm
  have hnotF : ∀ x ∈ closure ({C₀.point} : Set X), x ∉ F.supp := by
    intro x hx hxF
    obtain ⟨E, hE0, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
    have hE1 : 1 ≤ B.coeff E := by
      rw [hFdef, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown] at hE0
      have h0 : 0 ≤ ⌊B.coeff E⌋ := Int.floor_nonneg.mpr (coeff_mem_Icc hdlt E).1
      have hne : ⌊B.coeff E⌋ ≠ 0 := fun h => hE0 (by rw [h]; rfl)
      exact_mod_cast Int.le_floor.mp (show (1 : ℤ) ≤ ⌊B.coeff E⌋ by omega)
    exact Set.disjoint_left.mp (hdisj E hE1) hxE (hsub hx)
  have hF0 : 0 ≤ F := Finsupp.le_def.mpr fun P => by
    change (0 : ℚ) ≤ ((B.roundDown P : ℤ) : ℚ)
    rw [DivisorWithCoeffs.roundDown, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply]
    exact_mod_cast Int.floor_nonneg.mpr (coeff_mem_Icc hdlt P).1
  have hFC₀ : F.intersectionNumber ℂ sX C₀.ι C₀.dim_le hFq = 0 :=
    ((MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX F hFq hF0 C₀
      (hnotF _ (subset_closure rfl))).2).2 fun x hx =>
        hnotF x (specializes_iff_mem_closure.mp hx)
  -- `K + C` is negative on the ray
  have hKC : (Divisor.toQDivisor K + C).intersectionNumber ℂ sX C₀.ι C₀.dim_le hKCq =
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sX C₀.ι C₀.dim_le hKBq := by
    have h1 : ((Divisor.toQDivisor K + B) + (-(1 / 2) : ℚ) • F).IsQCartier :=
      isQCartier_of_isQFactorial sX hQ _
    rw [MMP.Fourfold.intersectionNumber_congr sX C₀.ι C₀.dim_le hKCq h1
        (by rw [hCF, sub_eq_add_neg, ← neg_smul, add_assoc]),
      MMP.Mori.QDivisor.intersectionNumber_add' ℂ sX C₀.ι C₀.dim_le _ _ hKBq hsF h1,
      MMP.Fourfold.intersectionNumber_smul sX C₀.ι C₀.dim_le F hFq _ hsF, hFC₀]
    ring
  have hRC : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + C) (curveRay C₀) := by
    refine ⟨hKCq, hR.2.1, ?_⟩
    rintro u ⟨c, hc, rfl⟩ hu
    have hc0 : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact hu (zero_smul _ _))
    have hne : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0 := fun h => hu (by rw [h, smul_zero])
    have hneg := hR.2.2 _ ⟨1, zero_le_one, one_smul _ _⟩ hne
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at hneg
    rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle, hKC]
    exact mul_neg_of_pos_of_neg hc0 hneg
  -- the flip of `K + B` is the flip of `K + C`
  have hFoC : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + C) f fp :=
    IsFlipOf.of_isNegativeExtremalRayOf hX hQ hCklt ⟨3, hK⟩ hRC hRc hRC hR hFo
  have heqC : logCanonicalDivisor K (QDivisor.toRDivisor C) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + C) := logCanonicalDivisor_toRDivisor K C
  have htrC : RationalMap.transformDivisor g (logCanonicalDivisor K (QDivisor.toRDivisor C)) =
      QDivisor.toRDivisor (flipTransform f fp (Divisor.toQDivisor K + C)) := by
    rw [heqC, ← transformDivisor_eq_flipTransform_of_isSmall hZ hE.isNormalVariety_source
      hF.isNormalVariety_flip hs hF.isSmall hF.isModificationOf.2]
    exact mapPrimeDivisors_mapCoeffsAddMonoidHom _ _ _
  have hantiC : MMP.Flips.IsRelativelyAmple f (-(logCanonicalDivisor K (QDivisor.toRDivisor C))) := by
    rw [heqC, ← map_neg]
    exact isRelativelyAmple_of_hasRelativelyAmpleMultiple hFoC.hasRelativelyAmpleMultiple
  have hcartC : IsCartierCombination (logCanonicalDivisor K (QDivisor.toRDivisor C)) :=
    heqC ▸ isCartierCombination_toRDivisor hKCq
  refine ⟨{ isNormalVariety_source := hE.isNormalVariety_source
            isNormalVariety_target := hE.isNormalVariety_target
            isCartierCombination := hcartC
            isContraction := hE.isContraction
            isRelativelyAntiAmple := hantiC
            relativePicardNumber_eq_one := hE.relativePicardNumber_eq_one },
    { hF with
      isCartierCombination := hcartC
      isRelativelyAntiAmple := hantiC
      isCartierCombination_transform := htrC ▸ isCartierCombination_toRDivisor hFoC.isQCartier_flip
      isRelativelyAmple_transform :=
        htrC ▸ isRelativelyAmple_of_hasRelativelyAmpleMultiple hFoC.hasRelativelyAmpleMultiple_flip },
    ?_⟩
  -- lowering the boundary commutes with the strict transform
  have htr : ∀ D : QDivisor X, RationalMap.transformDivisor g D = flipTransform f fp D :=
    transformDivisor_eq_flipTransform_of_isSmall hZ hE.isNormalVariety_source
      hF.isNormalVariety_flip hs hF.isSmall hF.isModificationOf.2
  rw [htr, htr, hCdef, lowerBoundary, lowerBoundary,
    flipTransform_mapCoeffs hZ hE.isNormalVariety_source hs hF.isSmall]

end Step

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hB : B.IsEffective) (hdlt : MMP.Intersection.IsDltPair sX B)
    (S : SequenceOfFlips sX 3 K B)
    (hmodel : ∀ i : ℕ, (i : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)),
    S.Terminates := by
  intro X _ _ _ _ sX _ K B hX hdim hQ hB hdlt S hmodel hbase
  by_contra hS
  have hinf : S.length = ⊤ := not_lt_top_iff.mp hS
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hinf ▸ ENat.coe_lt_top i
  haveI hI : ∀ i, IsIntegral (S.model i).1 := fun i =>
    (S.isNormalVariety_model i (hlt i)).1.toIsIntegral
  haveI := S.isLocallyNoetherian_model
  haveI := S.isNormal_model
  haveI := S.compactSpace_model
  have hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1 := fun i => hmodel i (hlt i)
  have hZ : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i) := fun i => hbase i (hlt (i + 1))
  have hK : ∀ i, (S.model i).2.2.1.IsCanonicalDivisor (S.model i).2.1 3 := fun i =>
    S.isCanonicalDivisor_model i (hlt i)
  have hflip : ∀ i, IsFlipOf (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
      (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) (S.contraction i) (S.flip i) :=
    fun i => isFlipOf_step S (hproj i) (hproj (i + 1)) (hZ i) (hlt (i + 1))
  have hBtr : ∀ i, (S.model (i + 1)).2.2.2 =
      flipTransform (S.contraction i) (S.flip i) (S.model i).2.2.2 := fun i =>
    model_boundary_eq_flipTransform S i (hlt (i + 1))
  have hdimm : ∀ i, topologicalKrullDim (S.model i).1 = 3 := topologicalKrullDim_model S hlt hdim
  have hray : ∀ i, ∃ C₀ : ProperCurve (S.model i).2.1, C₀.IsContractedBy (S.contraction i) ∧
      IsNegativeExtremalRayOf (S.model i).2.1
        (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) (curveRay C₀) ∧
      IsContractionOfRay (S.model i).2.1 (S.baseStr i) (curveRay C₀) (S.contraction i) := fun i =>
    exists_curveRay (hproj i) (hZ i) (hflip i).isContraction (hflip i).isQCartier
      (hflip i).hasRelativelyAmpleMultiple
      (S.isNegativeExtremalContraction i (hlt (i + 1))).relativePicardNumber_eq_one
  choose C₀ hC₀ hR hRc using hray
  -- the initial model is `(X, B)`
  have h0 : IsQFactorial (S.model 0).2.1 ∧
      MMP.Intersection.IsDltPair (S.model 0).2.1 (S.model 0).2.2.2 := by
    have key : ∀ M : FlipModel ℂ, M = ⟨X, sX, K, B⟩ → ∀ (_ : IsIntegral M.1)
        (_ : IsLocallyNoetherian M.1) (_ : IsNormal M.1),
        IsQFactorial M.2.1 ∧ MMP.Intersection.IsDltPair M.2.1 M.2.2.2 := by
      rintro M rfl _ _ _; exact ⟨hQ, hdlt⟩
    exact key _ S.model_zero _ _ _
  -- flips preserve `ℚ`-factoriality and dlt
  have hstep : ∀ i, IsQFactorial (S.model i).2.1 ∧
      MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2 := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih =>
      exact IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair (k := ℂ)
        (sV := S.baseStr i) (sX' := (S.model (i + 1)).2.1) (Δ' := (S.model (i + 1)).2.2.2)
        ⟨⟨hproj i, ih.1, ⟨3, hK i⟩, ih.2⟩, hR i, hRc i,
          (hflip i).isSmallMorphism.isBirationalMorphism, (hflip i).isSmallMorphism_flip.comp_eq,
          hBtr i, Or.inl ⟨(hflip i).isSmallMorphism, hflip i⟩⟩
  -- special termination
  obtain ⟨N, hN⟩ := exists_forall_ge_disjoint_exceptionalSet_of_isFlipOf (k := ℂ)
    (X := fun i => (S.model i).1) (Z := S.base) (sX := fun i => (S.model i).2.1)
    (sZ := S.baseStr) (f := S.contraction) (fp := S.flip) (K := fun i => (S.model i).2.2.1)
    (B := fun i => (S.model i).2.2.2) (R := fun i => curveRay (C₀ i)) hproj h0.1 h0.2 hK hR hRc
    hflip hBtr
  -- the lowered tail
  have htail : ∀ i, N ≤ i →
      IsNegativeExtremalContraction ℂ (S.model i).2.1 (S.baseStr i)
        (logCanonicalDivisor (S.model i).2.2.1
          (QDivisor.toRDivisor (lowerBoundary (S.model i).2.2.2))) (S.contraction i) ∧
      IsFlip ℂ (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
        (logCanonicalDivisor (S.model i).2.2.1
          (QDivisor.toRDivisor (lowerBoundary (S.model i).2.2.2)))
        (S.contraction i) (S.flip i) (S.flipMap i) ∧
      lowerBoundary (S.model (i + 1)).2.2.2 =
        RationalMap.transformDivisor (S.flipMap i) (lowerBoundary (S.model i).2.2.2) := by
    intro i hi
    haveI : LocallyOfFiniteType (S.model i).2.1 :=
      (S.isNormalVariety_model i (hlt i)).1.toLocallyOfFiniteType
    obtain ⟨h1, h2, h3⟩ := tail_step (hproj i) (hstep i).1 (hstep i).2 (hK i)
      (S.isNegativeExtremalContraction i (hlt (i + 1))) (S.isSmall i (hlt (i + 1)))
      (S.isFlip i (hlt (i + 1))) (hflip i) (hC₀ i) (hR i) (hRc i) (hN i hi).1
    exact ⟨h1, h2, by rw [S.transform_eq i (hlt (i + 1))]; exact h3⟩
  haveI : LocallyOfFiniteType (S.model N).2.1 :=
    (S.isNormalVariety_model N (hlt N)).1.toLocallyOfFiniteType
  let T : SequenceOfFlips (S.model N).2.1 3 (S.model N).2.2.1
      (lowerBoundary (S.model N).2.2.2) :=
    { isNormalVariety := S.isNormalVariety_model N (hlt N)
      isCanonicalDivisor := ⟨_, _, hK N⟩
      isQCartier := ⟨_, _, isQCartier_of_isQFactorial _ (hstep N).1 _⟩
      length := ⊤
      one_le_length := le_top
      model := fun j => ⟨(S.model (N + j)).1, (S.model (N + j)).2.1, (S.model (N + j)).2.2.1,
        lowerBoundary (S.model (N + j)).2.2.2⟩
      model_zero := rfl
      isNormalVariety_model := fun j _ => S.isNormalVariety_model (N + j) (hlt _)
      isLocallyNoetherian_model := fun j => S.isLocallyNoetherian_model (N + j)
      isNormal_model := fun j => S.isNormal_model (N + j)
      compactSpace_model := fun j => S.compactSpace_model (N + j)
      isCanonicalDivisor_model := fun j _ => hK (N + j)
      base := fun j => S.base (N + j)
      baseStr := fun j => S.baseStr (N + j)
      contraction := fun j => S.contraction (N + j)
      flip := fun j => S.flip (N + j)
      flipMap := fun j => S.flipMap (N + j)
      isNegativeExtremalContraction := fun j _ => (htail (N + j) (Nat.le_add_right N j)).1
      isSmall := fun j _ => S.isSmall (N + j) (hlt _)
      isFlip := fun j _ => (htail (N + j) (Nat.le_add_right N j)).2.1
      transform_eq := fun j _ => (htail (N + j) (Nat.le_add_right N j)).2.2 }
  have hT := (forall_projectiveKltTerminationLevel_and_terminates).2 (S.model N).1
    (S.model N).2.1 (S.model N).2.2.1 (lowerBoundary (S.model N).2.2.2) (hproj N) (hdimm N)
    (hstep N).1 (isEffective_lowerBoundary (hstep N).2)
    (isKltPair_lowerBoundary (hstep N).1 (hstep N).2)
    (isKawamataLogTerminal_lowerBoundary (hK N) (hstep N).1 (hstep N).2) T
    (fun j _ => hproj (N + j)) (fun j _ => hZ (N + j))
  exact absurd hT (lt_irrefl _)

end Proof_thm_mmp_projective_threefold_dlt_flip_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Termination of projective dlt flips of threefolds.** Let `X` be a normal projective
`ℚ`-factorial complex threefold with canonical divisor `K` and `B` an effective `ℚ`-divisor with
`(X, B)` dlt. Every sequence of flips for `(X, B)` whose models `X_i` and contraction targets `Z_i`
are all projective terminates. -/
@[mmp "thm_mmp_projective_threefold_dlt_flip_termination"]
public theorem SequenceOfFlips.terminates_of_isDltPair
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hB : B.IsEffective) (hdlt : MMP.Intersection.IsDltPair sX B)
    (S : SequenceOfFlips sX 3 K B)
    (hmodel : ∀ i : ℕ, (i : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) :
    S.Terminates :=
      by revert X sX K B hX hdim hQ hB hdlt S hmodel hbase; first | exact Proof_thm_mmp_projective_threefold_dlt_flip_termination.solution | exact Proof_thm_mmp_projective_threefold_dlt_flip_termination.solution _ | exact Proof_thm_mmp_projective_threefold_dlt_flip_termination.solution _ _ | exact Proof_thm_mmp_projective_threefold_dlt_flip_termination.solution _ _ _ | exact Proof_thm_mmp_projective_threefold_dlt_flip_termination.solution _ _ _ _

end MMP.Fourfold
