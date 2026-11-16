module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Termination.DltStratumDiagrams
import MMP.AlgebraicGeometry.MMP.Contraction.DltLineBundleDescent
import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
import MMP.AlgebraicGeometry.MMP.Termination.StrataEventuallyBirational
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumAvoidsFlip
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.Topology.KrullDimensionProperClosed

/-!
# Special termination for projective dlt fourfolds

Let `X` be a normal projective `ℚ`-factorial complex fourfold with canonical divisor `K`, and let
`B` be a `ℚ`-divisor such that `(X, B)` is dlt. In an infinite sequence of flips of negative
extremal rays for `(X, B)`, with flipping contractions `φ_i : X_i ⟶ Z_i` and flips
`φ_i⁺ : X_{i+1} ⟶ Z_i`, the flipping locus `Ex(φ_i)` is eventually disjoint from the reduced
boundary `⌊B_i⌋`, and the flipped locus `Ex(φ_i⁺)` from `⌊B_{i+1}⌋`.

## Main results

* `MMP.Fourfold.SequenceOfFlips.eventually_disjoint_exceptionalSet_supp_roundDown`: special
  termination for projective `ℚ`-factorial dlt fourfolds.

## Implementation notes

A sequence of flips is `MMP.Flips.SequenceOfFlips sX 4 K B`: each step is a small
`(K_{X_i} + B_i)`-negative extremal contraction `φ_i` followed by its flip `φ_i⁺`, and `B_{i+1}`
is the transform of `B_i`; it is infinite when its length is `⊤`. The contractions of such a
sequence are not required to be contractions of extremal rays of the cone of curves of a projective
variety; "flips of negative extremal rays" is encoded by asking that every target `Z_i` be
projective, as in `MMP.Fourfold.SequenceOfFlips.terminates_of_isDltPair`. The flipping and
flipped loci are the exceptional sets `MMP.Flips.exceptionalSet` of `φ_i` and `φ_i⁺`, and the
reduced boundary is the support of the round-down `⌊B_i⌋`, which for a dlt boundary (coefficients
at most one) is the union of the components of coefficient one.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter

namespace Proof_thm_mmp_fourfold_special_termination

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}

/-- Step `i` of a sequence of flips *fixes the boundary strata whose dimension satisfies `p`*:
every such adjunction stratum of `(X_i, B_i)` is isomorphic, as a pair over `Z_i`, to one of
`(X_{i+1}, B_{i+1})`, and conversely. -/
private def StepFixes (S : SequenceOfFlips sX 4 K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (p : WithBot ℕ∞ → Prop) : Prop :=
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI : IsIntegral (S.model i).1 :=
    (S.isNormalVariety_model i (lt_of_le_of_lt (by exact_mod_cast i.le_succ) hi)).1.toIsIntegral
  haveI : IsIntegral (S.model (i + 1)).1 := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
  (∀ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T),
    IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT →
    IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) →
    p (topologicalKrullDim T) →
    ∃ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T') (e : T ≅ T'),
      IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' ∧
      IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) ∧
      ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT') ∧
  (∀ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T'),
    IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' →
    IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) →
    p (topologicalKrullDim T') →
    ∃ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T) (e : T ≅ T'),
      IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT ∧
      IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) ∧
      ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT')

/-- Fixing the strata of dimension `< d` and those of dimension `d` is fixing those of dimension
`< d + 1`. -/
private theorem StepFixes.lt_succ {S : SequenceOfFlips sX 4 K B} {i : ℕ}
    {hi : ((i + 1 : ℕ) : ℕ∞) < S.length} {d : ℕ} (h₁ : StepFixes S i hi (· < d))
    (h₂ : StepFixes S i hi (· = d)) : StepFixes S i hi (· < (d + 1 : ℕ)) := by
  have key : ∀ x : WithBot ℕ∞, x < ((d + 1 : ℕ) : WithBot ℕ∞) → x < d ∨ x = d := by
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact Or.inl (WithBot.bot_lt_coe _)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top => exact absurd hx (by simp)
      | coe n =>
        have : n < d + 1 := by exact_mod_cast hx
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · left; exact_mod_cast h
        · right; rw [h]; rfl
  refine ⟨fun T ι BT h1 h2 h3 => ?_, fun T' ι' BT' h1 h2 h3 => ?_⟩
  · rcases key _ h3 with h | h
    · exact h₁.1 T ι BT h1 h2 h
    · exact h₂.1 T ι BT h1 h2 h
  · rcases key _ h3 with h | h
    · exact h₁.2 T' ι' BT' h1 h2 h
    · exact h₂.2 T' ι' BT' h1 h2 h

/-- In a sequence of flips of infinite length starting at a fourfold, every model is a
fourfold. -/
private theorem topologicalKrullDim_model (S : SequenceOfFlips sX 4 K B)
    (hlt : ∀ m : ℕ, (m : ℕ∞) < S.length) (hX : topologicalKrullDim X = 4) (i : ℕ) :
    topologicalKrullDim (S.model i).1 = 4 := by
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

/-- **A proper morphism to a projective variety with a relatively ample Cartier divisor is
H-projective** (Stacks 087S and 0BCL): the divisor makes it quasi-projective, and the base
carries an ample invertible sheaf. -/
private theorem isProjectiveMorphism_of_isRelativelyAmpleCartier {Y Z : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z) [IsProper f] [LocallyOfFiniteType f]
    {L : MMP.Mori.Divisor Y} (hL : MMP.Flips.IsRelativelyAmpleCartier f L) :
    IsProjectiveMorphism f := by
  obtain ⟨hLc, hamp⟩ := hL
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hinv : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L.divisorialSheaf :=
    Stacks.InvertibleRankOneScheme.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one Y _
  have hqp : IsQuasiProjective f := ⟨⟨inferInstance, inferInstance⟩, L.divisorialSheaf, hinv,
    ⟨inferInstance, hamp⟩⟩
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨H, hH, hHa⟩ := exists_isAmple_of_isProjectiveMorphism sZ M hMa hZ.isProjective
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective f H hHa hqp, inferInstance⟩

/-- A proper morphism `f : Y ⟶ Z` over `k` carrying an `f`-ample `ℝ`-divisor, to a projective
variety, is H-projective. -/
private theorem isProjectiveMorphism_of_isRelativelyAmple {Y Z : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z) [IsProper f] [LocallyOfFiniteType f]
    {A : RDivisor Y} (hA : MMP.Flips.IsRelativelyAmple f A) : IsProjectiveMorphism f := by
  obtain ⟨m, r, L, hm, -, hL, -⟩ := hA
  exact isProjectiveMorphism_of_isRelativelyAmpleCartier hZ f (hL ⟨0, hm⟩)

/-- A normal variety which is H-projective over a projective variety is projective. -/
private theorem isProjectiveVariety_of_isProjectiveMorphism {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : Y ⟶ Z} (hf : IsProjectiveMorphism f)
    (hfs : f ≫ sZ = sY) : MMP.Mori.IsProjectiveVariety ℂ sY :=
  (MMP.Mori.isProjectiveVariety_iff ℂ sY).2 ⟨hY.1, hfs ▸ IsProjectiveMorphism.comp hf hZ.isProjective⟩

/-- Every model of an infinite sequence of flips with projective contraction targets is
projective. -/
private theorem isProjectiveVariety_model [LocallyOfFiniteType sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (S : SequenceOfFlips sX 4 K B)
    (hinf : S.length = ⊤) (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (i : ℕ) : MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1 := by
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hinf ▸ ENat.coe_lt_top i
  cases i with
  | zero =>
    have key : ∀ M : FlipModel ℂ, M = ⟨X, sX, K, B⟩ → MMP.Mori.IsProjectiveVariety ℂ M.2.1 := by
      rintro M rfl; exact hX
    exact key _ S.model_zero
  | succ i =>
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    have hF := S.isFlip i (hlt (i + 1))
    have hv := hF.isNormalVariety_flip
    haveI : IsProper (S.flip i) := hF.isProper
    have hcomp : S.flip i ≫ S.baseStr i = (S.model (i + 1)).2.1 := hF.isSmall.comp_eq
    haveI : LocallyOfFiniteType (S.model (i + 1)).2.1 := hv.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (S.flip i ≫ S.baseStr i) := hcomp ▸ inferInstance
    haveI : LocallyOfFiniteType (S.flip i) := LocallyOfFiniteType.of_comp (g := S.baseStr i) inferInstance
    exact isProjectiveVariety_of_isProjectiveMorphism hv (hbase i)
      (isProjectiveMorphism_of_isRelativelyAmple (hbase i) _ hF.isRelativelyAmple_transform) hcomp

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
private theorem model_boundary_eq_flipTransform (S : SequenceOfFlips sX 4 K B)
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
private theorem isFlipOf_step (S : SequenceOfFlips sX 4 K B)
    (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
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
          isProjectiveMorphism := isProjectiveMorphism_of_isRelativelyAmple (hbase i) _
            hE.isRelativelyAntiAmple
          surjective := surjective_of_isProper_of_isDominant _
          isIso_app := hE.isContraction.isIso_app }
      isSmallMorphism := ⟨hE.isNormalVariety_source, hZ, hs.comp_eq, inferInstance, hb,
        two_le_closedsCodimension_exceptionalSet_of_isSmall hs⟩
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_of_isRelativelyAmple
        (by rw [map_neg, ← heq]; exact hE.isRelativelyAntiAmple)
      isSmallMorphism_flip := ⟨hF.isNormalVariety_flip, hZ, hs'.comp_eq, inferInstance,
        hs'.isBirationalMorphism, two_le_closedsCodimension_exceptionalSet_of_isSmall hs'⟩
      isProjectiveMorphism_flip := isProjectiveMorphism_of_isRelativelyAmple (hbase i) _
        hF.isRelativelyAmple_transform
      isQCartier_flip := QDivisor.isQCartier_of_isCartierCombination
        (htr ▸ hF.isCartierCombination_transform)
      hasRelativelyAmpleMultiple_flip := hasRelativelyAmpleMultiple_of_isRelativelyAmple
        (htr ▸ hF.isRelativelyAmple_transform) }

/-- `(φ⁺)⁻¹_* φ_*` commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor {Y Y' Z : Scheme.{0}} (f : Y ⟶ Z) (fp : Y' ⟶ Z)
    (D : Divisor Y) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, Divisor.toQDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- `(φ⁺)⁻¹_* φ_*` commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem flipTransform_toRDivisor {Y Y' Z : Scheme.{0}} (f : Y ⟶ Z) (fp : Y' ⟶ Z)
    (D : QDivisor Y) :
    flipTransform f fp (QDivisor.toRDivisor D) = QDivisor.toRDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, QDivisor.toRDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- A `(K + D)`-flip in the sense of `MMP.Fourfold.IsFlipOf`, for a canonical divisor `K`, is a
`(K + D)`-flip in the sense of Kollár–Mori, with canonical divisor `(f⁺)⁻¹_* f_* K` on the flip. -/
private theorem isFlip_of_isFlipOf {k : Type} [Field k] {Y Y' Z : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    {sY : Y ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {n : ℕ}
    {KY : Divisor Y} {D : QDivisor Y} {f : Y ⟶ Z} {fp : Y' ⟶ Z}
    (hK : KY.IsCanonicalDivisor sY n)
    (h : IsFlipOf sY sZ sY' (Divisor.toQDivisor KY + D) f fp) :
    MMP.Mori.IsFlip sY sZ sY' KY D f fp := by
  have hD : Divisor.toQDivisor (flipTransform f fp KY) + flipTransform f fp D =
      flipTransform f fp (Divisor.toQDivisor KY + D) := by
    rw [map_add, flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := h.isSmallMorphism.isNormalVariety_source
          isNormalVariety_target := h.isSmallMorphism.isNormalVariety_target
          comp_eq := h.isSmallMorphism.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := h.isQCartier
          isProper := h.isSmallMorphism.isProper
          isBirationalMorphism := h.isSmallMorphism.isBirationalMorphism
          two_le_codimension := h.isSmallMorphism.two_le_codimension
          hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
      isNormalVariety := h.isSmallMorphism_flip.isNormalVariety_source
      comp_eq := h.isSmallMorphism_flip.comp_eq
      isProper := h.isSmallMorphism_flip.isProper
      isBirationalMorphism := h.isSmallMorphism_flip.isBirationalMorphism
      isQCartier := hD ▸ h.isQCartier_flip
      hasRelativelyAmpleMultiple := hD ▸ h.hasRelativelyAmpleMultiple_flip
      two_le_codimension := h.isSmallMorphism_flip.two_le_codimension }

/-- Every model of an infinite sequence of flips of a dlt pair, with projective contraction
targets, is dlt: flips preserve dlt pairs (Kollár–Mori 3.44). -/
private theorem isDltPair_model [LocallyOfFiniteType sX]
    (hdlt : MMP.Intersection.IsDltPair sX B) (S : SequenceOfFlips sX 4 K B)
    (hinf : S.length = ⊤) (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (i : ℕ) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI : IsIntegral (S.model i).1 :=
      (S.isNormalVariety_model i (hinf ▸ ENat.coe_lt_top i)).1.toIsIntegral
    MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2 := by
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hinf ▸ ENat.coe_lt_top i
  induction i with
  | zero =>
    have key : ∀ M : FlipModel ℂ, M = ⟨X, sX, K, B⟩ → ∀ (_ : IsLocallyNoetherian M.1)
        (_ : IsNormal M.1) (_ : IsIntegral M.1), MMP.Intersection.IsDltPair M.2.1 M.2.2.2 := by
      rintro M rfl _ _ _; exact hdlt
    exact key _ S.model_zero _ _ _
  | succ i ih =>
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i (hlt i)).1.toIsIntegral
    haveI : IsIntegral (S.model (i + 1)).1 :=
      (S.isNormalVariety_model (i + 1) (hlt (i + 1))).1.toIsIntegral
    have hK := S.isCanonicalDivisor_model i (hlt i)
    have hmori := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hK _).1 ih
    have hfl := isFlip_of_isFlipOf hK (isFlipOf_step S hbase i (hlt (i + 1)))
    have hK' := hfl.isCanonicalDivisor_flipTransform hK
    rw [model_boundary_eq_flipTransform S i (hlt (i + 1))]
    exact (MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hK' _).2 (hfl.isDltPair hmori)

/-! ### Points over an open on which a morphism is an isomorphism -/

section IsoOver

variable {Y Z : Scheme.{0}} (f : Y ⟶ Z) (W : Z.Opens) [IsIso (f ∣_ W)]

/-- Over an open `W` on which `f` is an isomorphism, every point of `W` has a preimage. -/
private theorem exists_apply_eq_of_isIso_morphismRestrict {z : Z} (hz : z ∈ W) :
    ∃ y : Y, f y = z := by
  refine ⟨((inv (f ∣_ W)) ⟨z, hz⟩ : (f ⁻¹ᵁ W).toScheme).1, ?_⟩
  have h1 := congrArg (fun g : W.toScheme ⟶ Z => g ⟨z, hz⟩)
    (show inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι ≫ f = W.ι by
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc])
  exact h1

/-- Over an open `W` on which `f` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq_of_isIso_morphismRestrict {y y' : Y} (hy : f y ∈ W)
    (h : f y = f y') : y = y' := by
  have hy' : f y' ∈ W := h ▸ hy
  have := (f ∣_ W).isOpenEmbedding.injective (a₁ := ⟨y, hy⟩) (a₂ := ⟨y', hy'⟩) (Subtype.ext (by
    change ((f ∣_ W) ≫ W.ι) ⟨y, hy⟩ = ((f ∣_ W) ≫ W.ι) ⟨y', hy'⟩
    rw [morphismRestrict_ι]; exact h))
  exact congrArg Subtype.val this

/-- Over an open `W` on which `f` is an isomorphism, `f` reflects specialization. -/
private theorem specializes_of_map_specializes_of_isIso {y y' : Y} (hy : f y ∈ W)
    (hy' : f y' ∈ W) (h : f y ⤳ f y') : y ⤳ y' := by
  let p : (f ⁻¹ᵁ W).toScheme := ⟨y, hy⟩
  let q : (f ⁻¹ᵁ W).toScheme := ⟨y', hy'⟩
  have hp : ((f ∣_ W) ≫ W.ι) p = f y := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ W) ≫ W.ι) q = f y' := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rw [← ((f ∣_ W) ≫ W.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
    exact h
  exact hpq.map (f ⁻¹ᵁ W).ι.continuous

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

/-- **Two closed immersions related by a local isomorphism.** Let `f : X ⟶ Z` and
`f⁺ : X⁺ ⟶ Z` be isomorphisms over an open `W`, and let `ι : T ⟶ X`, `ι⁺ : T⁺ ⟶ X⁺` be closed
immersions of reduced schemes whose ranges lie over `W` and have the same image in `Z`. Then
there is an isomorphism `e : T ≅ T⁺` with `ι ≫ f = e ≫ ι⁺ ≫ f⁺`: transporting `ι⁺` through the
isomorphisms over `W` gives a second closed immersion into `X` with the range of `ι`. -/
private theorem exists_iso_comp_eq_of_isIso_morphismRestrict {T T' X X' Z : Scheme.{0}}
    [IsReduced T] [IsReduced T'] (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι]
    [IsClosedImmersion ι'] (f : X ⟶ Z) (fp : X' ⟶ Z) (W : Z.Opens) [IsIso (f ∣_ W)]
    [IsIso (fp ∣_ W)] (hι' : Set.range ι' ⊆ (fp ⁻¹ᵁ W : Set X'))
    (hrange : f '' Set.range ι = fp '' Set.range ι') :
    ∃ e : T ≅ T', ι ≫ f = e.hom ≫ ι' ≫ fp := by
  have hι : Set.range ι ⊆ (f ⁻¹ᵁ W : Set X) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨_, ⟨t', rfl⟩, ht'⟩ := (hrange ▸ Set.mem_image_of_mem f ⟨t, rfl⟩ :
      f (ι t) ∈ fp '' Set.range ι')
    change f (ι t) ∈ W
    rw [← ht']; exact hι' ⟨t', rfl⟩
  have hι'' : Set.range ι' ⊆ Set.range (fp ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]; exact hι'
  let κ : T' ⟶ X := IsOpenImmersion.lift (fp ⁻¹ᵁ W).ι ι' hι'' ≫ (fp ∣_ W) ≫
    inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι
  have hκ : κ ≫ f = ι' ≫ fp := by
    simp only [κ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
  have hrκ : Set.range κ = Set.range ι := by
    have hκW : Set.range κ ⊆ (f ⁻¹ᵁ W : Set X) := by
      rintro _ ⟨t, rfl⟩
      change f (κ t) ∈ W
      rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
      exact hι' ⟨t, rfl⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      have : f (κ t) ∈ f '' Set.range ι := by
        rw [hrange, ← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
        exact ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨_, ⟨s, rfl⟩, hs⟩ := this
      exact ⟨s, eq_of_apply_eq_of_isIso_morphismRestrict f W (hι ⟨s, rfl⟩) hs⟩
    · rintro _ ⟨s, rfl⟩
      have : f (ι s) ∈ fp '' Set.range ι' := hrange ▸ ⟨_, ⟨s, rfl⟩, rfl⟩
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := this
      refine ⟨t, eq_of_apply_eq_of_isIso_morphismRestrict f W (hκW ⟨t, rfl⟩) ?_⟩
      rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply, ht]
  haveI : IsPreimmersion (IsOpenImmersion.lift (fp ⁻¹ᵁ W).ι ι' hι'') := by
    have : IsPreimmersion (IsOpenImmersion.lift (fp ⁻¹ᵁ W).ι ι' hι'' ≫ (fp ⁻¹ᵁ W).ι) := by
      rw [IsOpenImmersion.lift_fac]; infer_instance
    exact IsPreimmersion.of_comp _ (fp ⁻¹ᵁ W).ι
  haveI : IsPreimmersion κ := by dsimp only [κ]; infer_instance
  haveI : IsClosedImmersion κ :=
    IsClosedImmersion.of_isPreimmersion κ (hrκ ▸ ι.isClosedEmbedding.isClosed_range)
  have hker : κ.ker = ι.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      hrκ]
  haveI := IsClosedImmersion.isIso_lift κ ι hker
  refine ⟨asIso (IsClosedImmersion.lift κ ι hker.le), ?_⟩
  rw [asIso_hom, ← hκ, IsClosedImmersion.lift_fac_assoc]

/-- **A point stratum over the common isomorphism locus is a point stratum on the other side.**
Let `f : X ⟶ Z` (proper) and `f⁺ : X⁺ ⟶ Z` be isomorphisms over an open `W`, and suppose every
prime divisor `P` of `X` has a prime divisor `P⁺` of `X⁺` over the same point of `Z` with the
same coefficient in `B⁺` as `P` in `B`. If `{x}` is a boundary stratum of `(X, B)` with
`f(x) ∈ W`, then the point `y` of `X⁺` over `f(x)` is a boundary stratum `{y}` of `(X⁺, B⁺)`:
membership in the components and maximality are local properties near `x` and `y`, carried over
by the isomorphisms over `W`. -/
private theorem exists_isDltStratum_singleton_of_isIso_morphismRestrict {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {B : QDivisor X} {B' : QDivisor X'}
    (f : X ⟶ Z) (fp : X' ⟶ Z) [IsProper f] (W : Z.Opens) [IsIso (f ∣_ W)] [IsIso (fp ∣_ W)]
    (hcorr : ∀ P : MMP.Mori.PrimeDivisor X, ∃ P' : MMP.Mori.PrimeDivisor X',
      f P.genericPoint = fp P'.genericPoint ∧ B'.coeff P' = B.coeff P)
    (hB' : MMP.Intersection.IsDltPair sX' B') {x : X} (hx : f x ∈ W)
    (hs : IsDltStratum sX B {x}) :
    ∃ y : X', fp y = f x ∧ IsDltStratum sX' B' {y} := by
  classical
  obtain ⟨-, J, hJne, hJ1, -, hmax⟩ := hs
  choose σ hσ using hcorr
  obtain ⟨y, hy⟩ := exists_apply_eq_of_isIso_morphismRestrict fp W hx
  have hyW : fp y ∈ W := hy ▸ hx
  have hmem : ∀ (P : MMP.Mori.PrimeDivisor X) (u : X) (v : X'), f u ∈ W → f u = fp v →
      (u ∈ (P.support : Set X) ↔ v ∈ ((σ P).support : Set X')) := by
    intro P u v hu huv
    have hv : fp v ∈ W := huv ▸ hu
    rw [P.support_eq_closure, (σ P).support_eq_closure, ← specializes_iff_mem_closure,
      ← specializes_iff_mem_closure]
    constructor
    · intro h
      have h1 : fp (σ P).genericPoint ⤳ fp v := by
        rw [← (hσ P).1, ← huv]; exact h.map f.continuous
      exact specializes_of_map_specializes_of_isIso fp W (h1.mem_open W.isOpen hv) hv h1
    · intro h
      have h1 : f P.genericPoint ⤳ f u := by
        rw [(hσ P).1, huv]; exact h.map fp.continuous
      exact specializes_of_map_specializes_of_isIso f W (h1.mem_open W.isOpen hu) hu h1
  have hclosedJ : ∀ (J : Finset (MMP.Mori.PrimeDivisor X')),
      IsClosed (⋂ P ∈ J, (P.support : Set X')) := fun J =>
    isClosed_biInter fun P _ => by rw [P.support_eq_closure]; exact isClosed_closure
  have hclosedJX : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
    isClosed_biInter fun P _ => by rw [P.support_eq_closure]; exact isClosed_closure
  have hxc : IsClosed ({x} : Set X) := by
    have := hmax.2 ⟨isIrreducible_singleton.closure,
      closure_minimal hmax.1.2 hclosedJX⟩ subset_closure
    exact closure_subset_iff_isClosed.1 this
  have hzc : IsClosed ({f x} : Set Z) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hxc
  have hyc : IsClosed ({y} : Set X') := by
    refine closure_subset_iff_isClosed.1 fun t ht => ?_
    have h1 : fp y ⤳ fp t := (specializes_iff_mem_closure.2 ht).map fp.continuous
    have h2 : fp t ∈ ({f x} : Set Z) := by
      rw [← hy]; exact (hy ▸ hzc).closure_subset (specializes_iff_mem_closure.1 h1)
    exact (eq_of_apply_eq_of_isIso_morphismRestrict fp W hyW (h2.trans hy.symm).symm).symm
  have hyJ : y ∈ ⋂ P' ∈ J.image σ, (P'.support : Set X') := by
    simp only [Finset.mem_image, Set.mem_iInter, forall_exists_index, and_imp]
    rintro _ P hP rfl
    exact (hmem P x y hx hy.symm).1 (Set.mem_iInter₂.1 (hmax.1.2 rfl) P hP)
  refine ⟨y, hy, hB', J.image σ, hJne.image σ, ?_, ⟨y, hyJ⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
    rw [(hσ P).2]; exact hJ1 P hP
  · refine ⟨⟨isIrreducible_singleton, Set.singleton_subset_iff.2 hyJ⟩, fun T hT hyT => ?_⟩
    have hξ := hT.1.isGenericPoint_genericPoint_closure
    set ξ := hT.1.genericPoint
    have hξy : ξ ⤳ y := hξ.specializes (subset_closure (hyT rfl))
    have hξW : fp ξ ∈ W := (hξy.map fp.continuous).mem_open W.isOpen hyW
    have hξJ : ξ ∈ ⋂ P' ∈ J.image σ, (P'.support : Set X') :=
      closure_minimal hT.2 (hclosedJ _) hξ.mem
    obtain ⟨ξ0, hξ0⟩ := exists_apply_eq_of_isIso_morphismRestrict f W hξW
    have hξ0W : f ξ0 ∈ W := hξ0 ▸ hξW
    have hξ0J : ξ0 ∈ ⋂ P ∈ J, (P.support : Set X) := by
      refine Set.mem_iInter₂.2 fun P hP => (hmem P ξ0 ξ hξ0W hξ0).2 ?_
      exact Set.mem_iInter₂.1 hξJ (σ P) (Finset.mem_image_of_mem σ hP)
    have hξ0x : ξ0 ⤳ x := specializes_of_map_specializes_of_isIso f W hξ0W hx (by
      rw [hξ0, ← hy]; exact hξy.map fp.continuous)
    have hcl := hmax.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hξ0J) hclosedJX⟩
      (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hξ0x))
    have hξ0eq : ξ0 = x := hcl (subset_closure rfl)
    have hξeq : ξ = y := eq_of_apply_eq_of_isIso_morphismRestrict fp W hξW (by
      rw [← hξ0, hξ0eq, hy])
    intro t ht
    have : t ∈ closure ({ξ} : Set X') := by rw [hξ.def]; exact subset_closure ht
    rwa [hξeq, hyc.closure_eq] at this

/-! ### The common isomorphism locus of a flip -/

section CommonLocus

variable {k : Type} [Field k] {X Z X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {E : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}

/-- Over the biregular locus of the contraction of a flip, the flip is an isomorphism. -/
private theorem biregularLocus_le_of_isFlip (hE : E.IsQCartier)
    (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g) :
    biregularLocus φ ≤ biregularLocus φp := by
  refine le_biregularLocus (IsFlip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hE
    hflip _ ?_)
  rw [Set.disjoint_left]
  rintro _ hzU ⟨x, hx, rfl⟩
  refine hx ⟨φ ⁻¹ᵁ biregularLocus φ, hzU, ?_⟩
  haveI : IsIso (φ ∣_ biregularLocus φ) := isBiregular_biregularLocus φ
  rw [← morphismRestrict_ι]
  infer_instance

/-- For small contractions, `(f)⁻¹_* f⁺_*` undoes `(f⁺)⁻¹_* f_*`. -/
private theorem flipTransform_flipTransform_of_isSmall [IsLocallyNoetherian Z] [IsNormal Z]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    (hs : IsSmall k sZ sX φ) (hs' : IsSmall k sZ sX' φp) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform φp φ (flipTransform φ φp D) = D := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall' hs hs' P
  rw [flipTransform_apply_of_isSmall hZ hX' hs' hs hP'.symm,
    flipTransform_apply_of_isSmall hZ hX hs hs' hP']

/-- **The reversed flip.** If `φ⁺ : X⁺ ⟶ Z` is an `E`-flip of `φ`, for a `ℚ`-Cartier `E`, then
`φ` is a `(-E⁺)`-flip of `φ⁺`, with `E⁺ = (φ⁺)⁻¹_* φ_* E`, along the inverse birational map
`X⁺ ⤏ X` over the common isomorphism locus. -/
private theorem exists_isFlip_symm (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g) :
    ∃ g' : X'.RationalMap X,
      IsFlip k sX' sZ sX (QDivisor.toRDivisor (-flipTransform φ φp E)) φp φ g' := by
  have hZ := hflip.isNormalVariety_target
  have hX := hflip.isNormalVariety_source
  have hX' := hflip.isNormalVariety_flip
  haveI : IsLocallyNoetherian Z := hZ.isLocallyNoetherian
  haveI : IsNormal Z := hZ.2
  haveI : IsProper φ := hflip.isContraction.isProper
  haveI : IsProper φp := hflip.isProper
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : IsIntegral X' := hX'.1.toIsIntegral
  have hs := hflip.isSmall_source
  have hs' := hflip.isSmall
  have htr : MMP.Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor E) =
      QDivisor.toRDivisor (flipTransform φ φp E) := by
    rw [transformDivisor_eq_flipTransform_of_isSmall hZ hX hX' hs hs' hflip.isModificationOf.2,
      flipTransform_toRDivisor]
  -- the inverse birational map over the common isomorphism locus
  obtain ⟨V, hV, hV', hXV, hX'V⟩ := MMP.Mori.exists_opens_isIso_of_isSmall hs hs'
  have hgen : ∀ (Y : Scheme.{0}) [IsIntegral Y], Order.coheight (genericPoint Y) ≤ 1 :=
    fun Y _ => (Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z).trans_le
      zero_le_one
  let e : X'.PartialIso X :=
    { source := φp ⁻¹ᵁ V
      dense_source := (φp ⁻¹ᵁ V).isOpen.dense ⟨_, hX'V _ (hgen X')⟩
      target := φ ⁻¹ᵁ V
      dense_target := (φ ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ (hgen X)⟩
      iso := asIso (φp ∣_ V) ≪≫ (asIso (φ ∣_ V)).symm }
  have key : e.iso.hom ≫ e.target.ι ≫ φ = e.source.ι ≫ φp := by
    change ((φp ∣_ V) ≫ inv (φ ∣_ V)) ≫ (φ ⁻¹ᵁ V).ι ≫ φ = (φp ⁻¹ᵁ V).ι ≫ φp
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
  have hover : MMP.Flips.RationalMap.IsOver φp φ e.toRationalMap := by
    rw [MMP.Flips.RationalMap.IsOver, Scheme.PartialIso.toRationalMap,
      ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
    change X'.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ φ =
      X'.homOfLE (le_top : e.source ≤ ⊤) ≫ X'.topIso.hom ≫ φp
    rw [Category.assoc, key]
    simp
  have htr' : MMP.Mori.RationalMap.transformDivisor e.toRationalMap
      (QDivisor.toRDivisor (-flipTransform φ φp E)) = -QDivisor.toRDivisor E := by
    rw [transformDivisor_eq_flipTransform_of_isSmall hZ hX' hX hs' hs hover, map_neg, map_neg,
      flipTransform_toRDivisor, flipTransform_flipTransform_of_isSmall hZ hX hX' hs hs']
  have hneg : ∀ {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {A : RDivisor Y},
      IsCartierCombination A → IsCartierCombination (-A) := by
    rintro Y _ _ A ⟨m, r, L, hL, rfl⟩
    exact ⟨m, -r, L, hL, by simp [Finset.sum_neg_distrib, neg_smul]⟩
  refine ⟨e.toRationalMap,
    { isNormalVariety_source := hX'
      isNormalVariety_target := hZ
      isNormalVariety_flip := hX
      isContraction := hs'.toIsBirationalContraction.toIsContraction
      isCartierCombination := by
        rw [map_neg, ← htr]; exact hneg hflip.isCartierCombination_transform
      isRelativelyAntiAmple := by
        change IsRelativelyAmple φp (-_)
        rw [map_neg, neg_neg, ← htr]; exact hflip.isRelativelyAmple_transform
      isProper := inferInstance
      isModificationOf := ⟨MMP.Mori.RationalMap.isBirational_toRationalMap e, hover⟩
      isMorphismInCodimOne :=
        MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX' φp φ _ hover
      isSmall := hs
      isCartierCombination_transform := by rw [htr']; exact hneg hflip.isCartierCombination
      isRelativelyAmple_transform := by rw [htr']; exact hflip.isRelativelyAntiAmple
      isSmall_source := hs' }⟩

/-- **The flip and its contraction have the same biregular locus** (the images of their
exceptional loci in `Z` agree, FA 7). -/
private theorem biregularLocus_eq_of_isFlip (hE : E.IsQCartier)
    (hflip : IsFlip k sX sZ sX' (QDivisor.toRDivisor E) φ φp g) :
    biregularLocus φ = biregularLocus φp := by
  refine le_antisymm (biregularLocus_le_of_isFlip hE hflip) ?_
  have hZ := hflip.isNormalVariety_target
  haveI : IsLocallyNoetherian Z := hZ.isLocallyNoetherian
  haveI : IsNormal Z := hZ.2
  obtain ⟨g', hg'⟩ := exists_isFlip_symm hflip
  have hE' : QDivisor.IsQCartier (-flipTransform φ φp E) := by
    have := hflip.isCartierCombination_transform
    rw [transformDivisor_eq_flipTransform_of_isSmall hZ hflip.isNormalVariety_source
      hflip.isNormalVariety_flip hflip.isSmall_source hflip.isSmall hflip.isModificationOf.2,
      flipTransform_toRDivisor] at this
    have h2 := MMP.Flips.QDivisor.IsQCartier.qsmul
      (QDivisor.isQCartier_of_isCartierCombination this) (-1)
    simpa using h2
  exact biregularLocus_le_of_isFlip hE' hg'

end CommonLocus

/-- In an integral scheme of dimension less than one, every point is the generic point. -/
private theorem eq_genericPoint_of_topologicalKrullDim_lt_one {T : Scheme.{0}} [IsIntegral T]
    (hn : topologicalKrullDim T < (1 : ℕ)) (x : T) : x = genericPoint T := by
  have h0 : topologicalKrullDim T ≤ 0 := by
    generalize topologicalKrullDim T = a at hn ⊢
    induction a using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd hn (by decide)
      | coe n =>
        have : n < 1 := by exact_mod_cast hn
        obtain rfl : n = 0 := by omega
        rfl
  have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 h0
  let Z : TopologicalSpace.IrreducibleCloseds T :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let U : TopologicalSpace.IrreducibleCloseds T :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hUZ : U ≤ Z := hmin U (fun _ _ => Set.mem_univ _)
  have hx : IsGenericPoint x ⊤ := by
    change closure {x} = Set.univ
    exact Set.eq_univ_of_univ_subset hUZ
  exact hx.eq (genericPoint_spec T)

/-- A scheme with a single point carries no prime divisor, so any two `ℚ`-divisors on it agree. -/
private theorem qDivisor_eq_of_subsingleton {T : Scheme.{0}} [Subsingleton T]
    (D D' : QDivisor T) : D = D' := by
  ext P
  exfalso
  have h := P.coheight_genericPoint
  rw [Order.coheight_eq_zero.mpr fun b _ => (Subsingleton.elim b P.genericPoint).le] at h
  exact zero_ne_one h

/-- **A point stratum away from the flipping locus is fixed.** Let `f : Y ⟶ Z` (proper) and
`f⁺ : Y⁺ ⟶ Z` be isomorphisms over an open `W`, with prime divisors of `Y` corresponding to prime
divisors of `Y⁺` over the same point of `Z` with the same boundary coefficients. If every boundary
stratum of `(Y, D)` meets `f⁻¹ W`, then every adjunction pair on a boundary stratum of dimension
`0` of `(Y, D)` is isomorphic over `Z` to one on a boundary stratum of `(Y⁺, D⁺)`. -/
private theorem exists_isStratumAdjunctionPair_of_topologicalKrullDim_lt_one {Y Y' Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {D : QDivisor Y} {D' : QDivisor Y'}
    (f : Y ⟶ Z) (fp : Y' ⟶ Z) [IsProper f] (W : Z.Opens) [IsIso (f ∣_ W)] [IsIso (fp ∣_ W)]
    (hcorr : ∀ P : MMP.Mori.PrimeDivisor Y, ∃ P' : MMP.Mori.PrimeDivisor Y',
      f P.genericPoint = fp P'.genericPoint ∧ D'.coeff P' = D.coeff P)
    (hD' : MMP.Intersection.IsDltPair sY' D')
    (hstr : ∀ T : Set Y, IsDltStratum sY D T → ∃ x ∈ T, f x ∈ W)
    (T : Scheme.{0}) (ι : T ⟶ Y) (BT : QDivisor T) (h1 : IsStratumAdjunctionPair sY D ι BT)
    (h2 : IsDltStratum sY D (Set.range ι.base)) (h3 : topologicalKrullDim T < (1 : ℕ)) :
    ∃ (T' : Scheme.{0}) (ι' : T' ⟶ Y') (BT' : QDivisor T') (e : T ≅ T'),
      IsStratumAdjunctionPair sY' D' ι' BT' ∧ IsDltStratum sY' D' (Set.range ι'.base) ∧
      ι ≫ f = e.hom ≫ ι' ≫ fp ∧ RationalMap.transformDivisor e.hom.toRationalMap BT = BT' := by
  have := h1.some.isClosedImmersion
  haveI : IsIntegral T := h1.some.isNormalVariety.1.toIsIntegral
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hstr _ h2
  have hrange : Set.range ι.base = {ι t} := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      rw [eq_genericPoint_of_topologicalKrullDim_lt_one h3 s,
        eq_genericPoint_of_topologicalKrullDim_lt_one h3 t]
      rfl
    · rintro rfl; exact ⟨t, rfl⟩
  obtain ⟨y, hy, hys⟩ := exists_isDltStratum_singleton_of_isIso_morphismRestrict f fp W hcorr hD'
    ht (hrange ▸ h2)
  obtain ⟨T', ι', BT', hrange', h1'⟩ :=
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hys).1.1
  have := h1'.some.isClosedImmersion
  haveI : IsIntegral T' := h1'.some.isNormalVariety.1.toIsIntegral
  obtain ⟨e, he⟩ := exists_iso_comp_eq_of_isIso_morphismRestrict ι ι' f fp W
    (by rw [hrange', Set.singleton_subset_iff]; change fp y ∈ W; rw [hy]; exact ht)
    (by rw [hrange, hrange', Set.image_singleton, Set.image_singleton, hy])
  haveI : Subsingleton T' := ⟨fun a b => ι'.isClosedEmbedding.injective <| by
    have ha : ι'.base a ∈ Set.range ι'.base := ⟨a, rfl⟩
    have hb : ι'.base b ∈ Set.range ι'.base := ⟨b, rfl⟩
    rw [hrange'] at ha hb
    exact ha.trans hb.symm⟩
  exact ⟨T', ι', BT', e, h1', hrange' ▸ hys, he, qDivisor_eq_of_subsingleton _ _⟩

/-- From the step `N` on which no boundary stratum is lost, the zero-dimensional strata are
fixed. -/
private theorem stepFixes_zero [LocallyOfFiniteType sX] (hdlt : MMP.Intersection.IsDltPair sX B)
    (S : SequenceOfFlips sX 4 K B) (hinf : S.length = ⊤)
    (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) (N : ℕ)
    (hN : ∀ i ≥ N, ((i + 1 : ℕ) : ℕ∞) < S.length →
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI : IsIntegral (S.model i).1 :=
        (S.isNormalVariety_model i (hinf ▸ ENat.coe_lt_top i)).1.toIsIntegral
      haveI : IsIntegral (S.model (i + 1)).1 :=
        (S.isNormalVariety_model (i + 1) (hinf ▸ ENat.coe_lt_top (i + 1))).1.toIsIntegral
      (∀ T : Set (S.model i).1, IsDltStratum (S.model i).2.1 (S.model i).2.2.2 T →
        ¬ T ⊆ (MMP.Mori.exceptionalSet (S.contraction i) : Set (S.model i).1)) ∧
      (∀ T' : Set (S.model (i + 1)).1,
        IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 T' →
        ¬ T' ⊆ (MMP.Mori.exceptionalSet (S.flip i) : Set (S.model (i + 1)).1)) ∧
      (∀ T : Set (S.model i).1, IsDltStratum (S.model i).2.1 (S.model i).2.2.2 T →
        ∃ T' : Set (S.model (i + 1)).1,
          IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 T' ∧
          closure ((S.contraction i).base '' T) = closure ((S.flip i).base '' T'))) :
    ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length, StepFixes S i hi (· < (1 : ℕ)) := by
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hinf ▸ ENat.coe_lt_top i
  rw [eventually_atTop]
  refine ⟨N, fun i hiN hi => ?_⟩
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.compactSpace_model (i + 1)
  haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i (hlt i)).1.toIsIntegral
  haveI : IsIntegral (S.model (i + 1)).1 :=
    (S.isNormalVariety_model (i + 1) (hlt (i + 1))).1.toIsIntegral
  obtain ⟨hstr, hstr', -⟩ := hN i hiN hi
  have hE := S.isNegativeExtremalContraction i hi
  have hF := S.isFlip i hi
  have hs := S.isSmall i hi
  have hs' := hF.isSmall
  have hZ := hE.isNormalVariety_target
  have hX := hE.isNormalVariety_source
  haveI : IsNormal (S.base i) := hZ.2
  haveI : LocallyOfFiniteType (S.baseStr i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (S.base i) := LocallyOfFiniteType.isLocallyNoetherian (S.baseStr i)
  haveI : IsProper (S.contraction i) := hs.isProper
  haveI : IsProper (S.flip i) := hF.isProper
  have heq := logCanonicalDivisor_toRDivisor (S.model i).2.2.1 (S.model i).2.2.2
  have hFQ := heq ▸ hF
  have hW := biregularLocus_eq_of_isFlip
    (QDivisor.isQCartier_of_isCartierCombination (heq ▸ hE.isCartierCombination)) hFQ
  haveI : IsIso (S.contraction i ∣_ biregularLocus (S.contraction i)) :=
    isBiregular_biregularLocus _
  haveI : IsIso (S.flip i ∣_ biregularLocus (S.contraction i)) := by
    rw [hW]; exact isBiregular_biregularLocus _
  have hB := model_boundary_eq_flipTransform S i hi
  have hdltm := isDltPair_model hdlt S hinf hbase
  refine ⟨fun T ι BT h1 h2 h3 => ?_, fun T' ι' BT' h1 h2 h3 => ?_⟩
  · refine exists_isStratumAdjunctionPair_of_topologicalKrullDim_lt_one (S.contraction i)
      (S.flip i) (biregularLocus (S.contraction i)) (fun P => ?_) (hdltm (i + 1))
      (fun T hT => ?_) T ι BT h1 h2 h3
    · obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall' hs hs' P
      refine ⟨P', hP', ?_⟩
      change (S.model (i + 1)).2.2.2 P' = (S.model i).2.2.2 P
      rw [hB]
      exact flipTransform_apply_of_isSmall hZ hX hs hs' hP' _
    · obtain ⟨x, hx, hxE⟩ := Set.not_subset.1 (hstr T hT)
      exact ⟨x, hx, not_not.1 hxE⟩
  · have hcorr : ∀ P : MMP.Mori.PrimeDivisor (S.model (i + 1)).1,
        ∃ P' : MMP.Mori.PrimeDivisor (S.model i).1,
          S.flip i P.genericPoint = S.contraction i P'.genericPoint ∧
            (S.model i).2.2.2.coeff P' = (S.model (i + 1)).2.2.2.coeff P := fun P => by
      obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall' hs' hs P
      refine ⟨P', hP', ?_⟩
      change (S.model i).2.2.2 P' = (S.model (i + 1)).2.2.2 P
      rw [hB]
      exact (flipTransform_apply_of_isSmall hZ hX hs hs' hP'.symm _).symm
    have hmeet : ∀ T : Set (S.model (i + 1)).1,
        IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 T →
          ∃ x ∈ T, S.flip i x ∈ biregularLocus (S.contraction i) := fun T hT => by
      obtain ⟨x, hx, hxE⟩ := Set.not_subset.1 (hstr' T hT)
      exact ⟨x, hx, hW ▸ not_not.1 hxE⟩
    obtain ⟨T₀, ι₀, BT₀, e, h1₀, h2₀, he, -⟩ :=
      exists_isStratumAdjunctionPair_of_topologicalKrullDim_lt_one (S.flip i) (S.contraction i)
        (biregularLocus (S.contraction i)) hcorr (hdltm i) hmeet T' ι' BT' h1 h2 h3
    haveI : IsIntegral T' := h1.some.isNormalVariety.1.toIsIntegral
    haveI : Subsingleton T' := ⟨fun a b => by
      rw [eq_genericPoint_of_topologicalKrullDim_lt_one h3 a,
        eq_genericPoint_of_topologicalKrullDim_lt_one h3 b]⟩
    refine ⟨T₀, ι₀, BT₀, e.symm, h1₀, h2₀, ?_, qDivisor_eq_of_subsingleton _ _⟩
    rw [Iso.symm_hom, he, Iso.inv_hom_id_assoc]

/-- The exceptional set of `MMP.Flips` (points near which `f` is not an open immersion) lies in
the exceptional set of `MMP.Mori` (points over the complement of the biregular locus). -/
private theorem flips_exceptionalSet_subset {Y W : Scheme.{0}} (f : Y ⟶ W) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy hy'
  refine hy ⟨f ⁻¹ᵁ MMP.Mori.biregularLocus f, hy', ?_⟩
  haveI : IsIso (f ∣_ MMP.Mori.biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

/-- A component of coefficient one of the boundary of a dlt pair is a boundary stratum. -/
private theorem isDltStratum_support {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {D : QDivisor Y} (hD : MMP.Intersection.IsDltPair sY D)
    (P : MMP.Mori.PrimeDivisor Y) (hP : D.coeff P = 1) :
    IsDltStratum sY D (P.support : Set Y) := by
  have hirr : IsIrreducible (P.support : Set Y) := by
    rw [P.support_eq_closure]; exact isIrreducible_singleton.closure
  refine ⟨hD, {P}, Finset.singleton_nonempty P, by simp [hP], ?_, ?_⟩
  · simpa using hirr.nonempty
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    exact ⟨⟨hirr, le_rfl⟩, fun T hT _ => hT.2⟩

/-- A point of the reduced boundary of a dlt pair lies on a component of coefficient one. -/
private theorem exists_coeff_eq_one_of_mem_supp_roundDown {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {D : QDivisor Y}
    (hD : MMP.Intersection.IsDltPair sY D) {y : Y}
    (hy : y ∈ ((DivisorWithCoeffs.roundDown D).supp : Set Y)) :
    ∃ P : MMP.Mori.PrimeDivisor Y, D.coeff P = 1 ∧ y ∈ (P.support : Set Y) := by
  obtain ⟨P, hP, hyP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hy
  refine ⟨P, ?_, hyP⟩
  have h0 : 0 ≤ D.coeff P := hD.1.2.1 P
  have h1 : D.coeff P ≤ 1 := hD.2.1 P
  by_contra hne
  exact hP (Int.floor_eq_zero_iff.2 ⟨h0, lt_of_le_of_ne h1 hne⟩)

/-- A closed subscheme onto a prime divisor of a variety of dimension four has dimension less
than four. -/
private theorem topologicalKrullDim_lt_four {Y T : Scheme.{0}} [IsIntegral Y]
    (hY : topologicalKrullDim Y = 4) (ι : T ⟶ Y) [IsClosedImmersion ι]
    (P : MMP.Mori.PrimeDivisor Y) (hι : Set.range ι.base = (P.support : Set Y)) :
    topologicalKrullDim T < (4 : ℕ) := by
  have hT : topologicalKrullDim T = topologicalKrullDim (P.support : Set Y) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    exact congrArg (fun s : Set Y => topologicalKrullDim s) hι
  have hclosed : IsClosed (P.support : Set Y) := by
    rw [P.support_eq_closure]; exact isClosed_closure
  have hne : (P.support : Set Y) ≠ Set.univ := by
    intro h
    have h1 := MMP.Mori.PrimeDivisor.codimension_closure_genericPoint P
    have h0 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 0 := by
      refine Order.coheight_eq_zero.mpr fun b _ => fun x _ => ?_
      change x ∈ closure ({P.genericPoint} : Set Y)
      rw [← P.support_eq_closure, h]; exact Set.mem_univ x
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hle : topologicalKrullDim (P.support : Set Y) ≤ 4 :=
    hY ▸ topologicalKrullDim_subspace_le Y _
  have hfin : topologicalKrullDim (P.support : Set Y) ≠ ⊤ := fun h => by
    rw [h] at hle; exact absurd hle (by decide)
  rw [hT]
  have := MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ hclosed hne hfin
  rw [hY] at this
  exact_mod_cast this

/-- For an isomorphism `e`, the inverse transform along `e` undoes the transform along `e`. -/
private theorem inverseTransformDivisor_transformDivisor {T T' : Scheme.{0}} [IsReduced T]
    [IsSeparated (T' ↘ Limits.terminal Scheme)] (e : T ≅ T') (D : QDivisor T) :
    inverseTransformDivisor e.hom (RationalMap.transformDivisor e.hom.toRationalMap D) = D := by
  ext P
  have hco : Order.coheight (e.hom P.genericPoint) = 1 := by
    rw [coheight_eq_of_isOpenImmersion e.hom]; exact P.coheight_genericPoint
  let Q : MMP.Mori.PrimeDivisor T' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = e.hom P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hbir : biregularLocus e.hom = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))
  have hinj : Function.Injective e.hom.base := (Scheme.homeoOfIso e).injective
  change DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor e.hom)
    (RationalMap.transformDivisor e.hom.toRationalMap D) P = D P
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (E := Q)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ.symm
      (by rw [hbir]; trivial))
    (fun Q' hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hQ.symm)]
  change DivisorWithCoeffs.mapPrimeDivisors
    (RationalMap.transformPrimeDivisor e.hom.toRationalMap) D Q = D P
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom P Q).mpr hQ.symm)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <| hinj <|
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom E' Q).mp hE').trans
        hQ) D

/-- **A fixed reduced boundary avoids the flip.** If a flip `f⁺` of `f` between projective dlt
fourfolds loses no boundary stratum, and fixes every boundary stratum of dimension less than
four in both directions, then `Ex(f)` misses `⌊B⌋` and `Ex(f⁺)` misses `⌊B⁺⌋`. -/
private theorem disjoint_of_stepFixes {Y Y' Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {KY : Divisor Y} {D : QDivisor Y} {D' : QDivisor Y'} {f : Y ⟶ Z} {fp : Y' ⟶ Z}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hY' : MMP.Mori.IsProjectiveVariety ℂ sY')
    (hdimY : topologicalKrullDim Y = 4) (hdimY' : topologicalKrullDim Y' = 4)
    (hK : KY.IsCanonicalDivisor sY 4)
    (hD : MMP.Intersection.IsDltPair sY D) (hD' : MMP.Intersection.IsDltPair sY' D')
    (hflip : IsFlipOf sY sZ sY' (Divisor.toQDivisor KY + D) f fp)
    (hDD' : D' = flipTransform f fp D)
    (hstr : ∀ T : Set Y, IsDltStratum sY D T → ¬ T ⊆ (MMP.Mori.exceptionalSet f : Set Y))
    (hstr' : ∀ T' : Set Y', IsDltStratum sY' D' T' → ¬ T' ⊆ (MMP.Mori.exceptionalSet fp : Set Y'))
    (hfix : ∀ (T : Scheme.{0}) (ι : T ⟶ Y) (BT : QDivisor T),
      IsStratumAdjunctionPair sY D ι BT → IsDltStratum sY D (Set.range ι.base) →
      topologicalKrullDim T < (4 : ℕ) →
      ∃ (T' : Scheme.{0}) (ι' : T' ⟶ Y') (BT' : QDivisor T') (e : T ≅ T'),
        IsStratumAdjunctionPair sY' D' ι' BT' ∧ IsDltStratum sY' D' (Set.range ι'.base) ∧
        ι ≫ f = e.hom ≫ ι' ≫ fp ∧ RationalMap.transformDivisor e.hom.toRationalMap BT = BT')
    (hfix' : ∀ (T' : Scheme.{0}) (ι' : T' ⟶ Y') (BT' : QDivisor T'),
      IsStratumAdjunctionPair sY' D' ι' BT' → IsDltStratum sY' D' (Set.range ι'.base) →
      topologicalKrullDim T' < (4 : ℕ) →
      ∃ (T : Scheme.{0}) (ι : T ⟶ Y) (BT : QDivisor T) (e : T ≅ T'),
        IsStratumAdjunctionPair sY D ι BT ∧ IsDltStratum sY D (Set.range ι.base) ∧
        ι ≫ f = e.hom ≫ ι' ≫ fp ∧ RationalMap.transformDivisor e.hom.toRationalMap BT = BT') :
    Disjoint (MMP.Flips.exceptionalSet f) ((DivisorWithCoeffs.roundDown D).supp : Set Y) ∧
      Disjoint (MMP.Flips.exceptionalSet fp) ((DivisorWithCoeffs.roundDown D').supp : Set Y') := by
  subst hDD'
  constructor
  · refine Set.disjoint_left.2 fun y hyE hyB => ?_
    obtain ⟨P, hP1, hyP⟩ := exists_coeff_eq_one_of_mem_supp_roundDown hD hyB
    have hPs := isDltStratum_support hD P hP1
    obtain ⟨T, ι, BT, hrange, hT⟩ :=
      (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hPs).1.1
    have := hT.some.isClosedImmersion
    obtain ⟨T', ι', BT', e, hT', -, hcomm, hBT⟩ :=
      hfix T ι BT hT (hrange ▸ hPs) (topologicalKrullDim_lt_four hdimY ι P hrange)
    haveI : IsIntegral T := hT.some.isNormalVariety.1.toIsIntegral
    haveI := isSeparated_toTerminal_of_isNormalVariety hT'.some.isNormalVariety
    have hdis := (IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair hY hY' hK hD hD'
      hflip hstr hstr' hT hT' e hcomm (by rw [← hBT]; exact inverseTransformDivisor_transformDivisor e BT)).1
    exact Set.disjoint_left.1 hdis (hrange ▸ hyP) (flips_exceptionalSet_subset f hyE)
  · refine Set.disjoint_left.2 fun y hyE hyB => ?_
    obtain ⟨P, hP1, hyP⟩ := exists_coeff_eq_one_of_mem_supp_roundDown hD' hyB
    have hPs := isDltStratum_support hD' P hP1
    obtain ⟨T', ι', BT', hrange, hT'⟩ :=
      (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hPs).1.1
    have := hT'.some.isClosedImmersion
    obtain ⟨T, ι, BT, e, hT, -, hcomm, hBT⟩ :=
      hfix' T' ι' BT' hT' (hrange ▸ hPs) (topologicalKrullDim_lt_four hdimY' ι' P hrange)
    haveI : IsIntegral T := hT.some.isNormalVariety.1.toIsIntegral
    haveI := isSeparated_toTerminal_of_isNormalVariety hT'.some.isNormalVariety
    have hdis := (IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair hY hY' hK hD hD'
      hflip hstr hstr' hT hT' e hcomm (by rw [← hBT]; exact inverseTransformDivisor_transformDivisor e BT)).2
    exact Set.disjoint_left.1 hdis (hrange ▸ hyP) (flips_exceptionalSet_subset fp hyE)

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) (hdlt : MMP.Intersection.IsDltPair sX B)
    (S : SequenceOfFlips sX 4 K B) (hinf : S.length = ⊤)
    (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)),
    ∀ᶠ i in atTop,
      Disjoint (MMP.Flips.exceptionalSet (S.contraction i))
          ((DivisorWithCoeffs.roundDown (S.model i).2.2.2).supp : Set (S.model i).1) ∧
        Disjoint (MMP.Flips.exceptionalSet (S.flip i))
          ((DivisorWithCoeffs.roundDown (S.model (i + 1)).2.2.2).supp :
            Set (S.model (i + 1)).1) := by
  intro X _ _ _ _ sX _ K B hX hdim hQ hdlt S hinf hbase
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hinf ▸ ENat.coe_lt_top i
  haveI hI : ∀ i, IsIntegral (S.model i).1 := fun i =>
    (S.isNormalVariety_model i (hlt i)).1.toIsIntegral
  haveI := S.isLocallyNoetherian_model
  haveI := S.isNormal_model
  haveI := S.compactSpace_model
  have hproj := isProjectiveVariety_model hX S hinf hbase
  have hdltm := isDltPair_model hdlt S hinf hbase
  have hdimm := topologicalKrullDim_model S hlt hdim
  -- the strata lost along the sequence
  obtain ⟨N, hN⟩ := exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum (k := ℂ)
    (X := fun i => (S.model i).1) (Z := S.base) (sX := fun i => (S.model i).2.1)
    (sZ := S.baseStr) (f := S.contraction) (fp := S.flip) (n := 4)
    (K := fun i => (S.model i).2.2.1) (B := fun i => (S.model i).2.2.2) (L := S.length)
    (hproj 0) (hdltm 0) (fun i _ => S.isCanonicalDivisor_model i (hlt i))
    (fun i hi => isFlipOf_step S hbase i hi) (fun i hi => model_boundary_eq_flipTransform S i hi)
  -- the strata of dimension `0, 1, 2, 3` are eventually fixed
  have h0 := stepFixes_zero hdlt S hinf hbase N hN
  have hstep : ∀ d : ℕ, 1 ≤ d → d ≤ 3 →
      (∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length, StepFixes S i hi (· < d)) →
      ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
        StepFixes S i hi (· < (d + 1 : ℕ)) := by
    intro d hd₁ hd₃ hfix
    have hnext := SequenceOfFlips.eventually_stratumAdjunctionPair_iso_of_projectiveLowerLogMMP
      projectiveLowerLogMMP_three hdim S (Eventually.of_forall fun i _ => hproj i)
      (Eventually.of_forall fun i _ => hbase i) (Eventually.of_forall fun i _ => hdltm i)
      d hd₁ hd₃ hfix
    filter_upwards [hfix, hnext] with i h₁ h₂ hi
    exact StepFixes.lt_succ (h₁ hi) (h₂ hi)
  have h4 := hstep 3 (by norm_num) le_rfl (hstep 2 (by norm_num) (by norm_num)
    (hstep 1 le_rfl (by norm_num) h0))
  filter_upwards [h4, eventually_ge_atTop N] with i hfix hiN
  have hi : ((i + 1 : ℕ) : ℕ∞) < S.length := hlt (i + 1)
  obtain ⟨hstr, hstr', -⟩ := hN i hiN hi
  exact disjoint_of_stepFixes (hproj i) (hproj (i + 1)) (hdimm i) (hdimm (i + 1))
    (S.isCanonicalDivisor_model i (hlt i)) (hdltm i) (hdltm (i + 1)) (isFlipOf_step S hbase i hi)
    (model_boundary_eq_flipTransform S i hi) hstr hstr' (hfix hi).1 (hfix hi).2

end Proof_thm_mmp_fourfold_special_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Special termination for projective dlt fourfolds.** Let `X` be a normal projective
`ℚ`-factorial complex fourfold with canonical divisor `K` and `B` a `ℚ`-divisor with `(X, B)`
dlt. In an infinite sequence of flips for `(X, B)` whose contraction targets `Z_i` are all
projective (flips of negative extremal rays), for all sufficiently large `i` the flipping
locus `Ex(φ_i) ⊆ X_i` is disjoint from `Supp ⌊B_i⌋` and the flipped locus `Ex(φ_i⁺) ⊆ X_{i+1}` is
disjoint from `Supp ⌊B_{i+1}⌋`. -/
@[mmp "thm_mmp_fourfold_special_termination"]
public theorem SequenceOfFlips.eventually_disjoint_exceptionalSet_supp_roundDown
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) (hdlt : MMP.Intersection.IsDltPair sX B)
    (S : SequenceOfFlips sX 4 K B) (hinf : S.length = ⊤)
    (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) :
    ∀ᶠ i in atTop,
      Disjoint (MMP.Flips.exceptionalSet (S.contraction i))
          ((DivisorWithCoeffs.roundDown (S.model i).2.2.2).supp : Set (S.model i).1) ∧
        Disjoint (MMP.Flips.exceptionalSet (S.flip i))
          ((DivisorWithCoeffs.roundDown (S.model (i + 1)).2.2.2).supp :
            Set (S.model (i + 1)).1) :=
              by revert X sX K B hX hdim hQ hdlt S hinf hbase; first | exact Proof_thm_mmp_fourfold_special_termination.solution | exact Proof_thm_mmp_fourfold_special_termination.solution _ | exact Proof_thm_mmp_fourfold_special_termination.solution _ _ | exact Proof_thm_mmp_fourfold_special_termination.solution _ _ _ | exact Proof_thm_mmp_fourfold_special_termination.solution _ _ _ _

end MMP.Fourfold
