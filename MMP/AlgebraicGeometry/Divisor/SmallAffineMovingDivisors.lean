module
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra

/-!
# Moving divisors on small modifications over an affine base

This file collects three facts about divisors used in the fourfold program.

* Let `X` be a normal variety with canonical divisor `K`, and `P₁, …, P_r` prime divisors. If
  `D_b = K + ∑ bᵢ Pᵢ` is `ℝ`-Cartier, then the `ℝ`-Cartier locus of `c ↦ D_c` is an affine
  subspace `V ∋ b` defined over `ℚ`, `D_c` is `ℚ`-Cartier at the rational points of `V`, and along
  every projective birational `f : W ⟶ X` the coefficients of `f^*D_c` are rational affine
  functions of `c ∈ V`. Neither `ℚ`-factoriality of `X` nor `ℚ`-Cartierness of `K` is assumed.
* Let `f : X ⟶ Z` be a small projective birational morphism of normal varieties with `Z` affine
  and `S` a prime divisor on `X`. Every divisor on `X` is linearly equivalent to an effective
  divisor not containing `S`: since `f` is biregular at the generic points of prime divisors,
  global functions of `Z` separate `η_S` from every other prime divisor, and multiplying by large
  powers of them clears all poles away from `S`.
* If moreover `X` is `ℚ`-factorial and the base field is algebraically closed of characteristic
  zero, every effective `ℚ`-divisor `B` not containing `S` decomposes as `B ∼_ℚ A₀ + B₀` with
  `A₀` in the class of an `f`-ample `A = H / r` and `B₀ = E / r ≥ 0` not containing `S`, where
  `E ∼ rB - H` is effective; general members of `|nH|` (Bertini) give representatives `A₀` with
  coefficients in `{0, 1/m}` for arbitrarily large `m`, avoiding finitely many given primes.

## Main results

* `MMP.Fourfold.exists_rat_affineSubspace_isCartierCombination_and_coeff_pullback_affine`
* `MMP.Fourfold.IsSmallMorphism.exists_linearlyEquivalent_coeff_eq_zero`
* `MMP.Fourfold.IsSmallMorphism.exists_qLinearlyEquivalent_add_of_isQFactorial`
* `MMP.Fourfold.exists_forall_exists_mem_nonvanishingLocus_of_isAmple`: a power `M^{⊗n}`, `n ≥ N`,
  of an ample invertible module has finitely many global sections with no common zero.
* `MMP.Mori.Divisor.IsCartier.nonempty_tensorPowModule_iso_divisorialSheaf_zsmul`:
  `𝒪_X(H)^{⊗ n} ≅ 𝒪_X(n H)` for a Cartier divisor `H`.

## Implementation notes

An affine subspace defined over `ℚ` is given as `b⁰ + span_ℝ {w₁, …, w_p}` with
`b⁰, wⱼ ∈ ℚ^r`. The pull-back `f^*D_c` is any `ℝ`-divisor `G` with
`MMP.Flips.IsRCartierPullback f D_c G`; it is unique along dominant morphisms, since
`Ca(X) ⊗_ℤ ℝ → Div(X)_ℝ` is injective. Real presentations of `ℝ`-Cartier divisors are recorded as
finitely supported functions `Ca(X) →₀ ℝ`.

The source moves a prime divisor through global generation of `f_* 𝒪_X(D)` on the affine `Z`;
the proof here uses only the global functions of `Z` and that `f` is biregular at the generic
points of prime divisors.

A general section of the free system `|nH|` has reduced zero scheme, so the coefficients of its
divisor are at most `1`: the principal stalk ideal `(π^a)` at the generic point of a prime is
radical, which forces `a ≤ 1`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.2, 2.5.1
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [OpenAI, *Projective lc fourfolds*][OAI4]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Mori.Divisor.IsCartier

/-- `𝒪_X(H)^{⊗ n} ≅ 𝒪_X(n • H)` for a Cartier divisor `H` and every `n : ℕ`. -/
public theorem nonempty_tensorPowModule_iso_divisorialSheaf_zsmul {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {H : Divisor X} (hH : H.IsCartier)
    [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf] (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ) ≅
      ((n : ℤ) • H).divisorialSheaf) := by
  induction n with
  | zero => exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫
      (eqToIso (by rw [Nat.cast_zero, zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hH.zsmul (n : ℤ)).divisorialSheafTensorIso hH ≪≫
      eqToIso (by congr 1; push_cast; simp only [add_smul, one_smul])⟩

end MMP.Mori.Divisor.IsCartier

namespace MMP.Fourfold

/-! ### A rational Cartier locus through a real adjoint divisor -/

section RationalCartierLocus

open TensorProduct MMP.Flips

/-- The tensor `∑ L ⊗ y L` attached to a finitely supported family of coefficients. -/
private noncomputable def toTensor (G : Type*) [AddCommGroup G] : (G →₀ ℝ) →+ G ⊗[ℤ] ℝ :=
  Finsupp.liftAddHom fun L => (TensorProduct.mk ℤ G ℝ L).toAddMonoidHom

private theorem rDivisorTensorMap_toTensor {G : Type*} [AddCommGroup G] {Y : Scheme.{u}}
    (g : G →+ Divisor Y) (y : G →₀ ℝ) :
    rDivisorTensorMap g (toTensor G y) =
      Finsupp.linearCombination ℝ (fun L => Divisor.toRDivisor (g L)) y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single L r => simp [toTensor, rDivisorTensorMap_tmul]

private theorem coeff_linearCombination_mapRange {G : Type*} {Y : Scheme.{u}}
    (v : G → Divisor Y) (y : G →₀ ℚ) (E : MMP.Mori.PrimeDivisor Y) :
    (Finsupp.linearCombination ℝ (fun L => Divisor.toRDivisor (v L))
      (Finsupp.mapRange.addMonoidHom (Rat.castHom ℝ).toAddMonoidHom y)).coeff E =
      ((Finsupp.linearCombination ℚ (fun L => Divisor.toQDivisor (v L)) y).coeff E : ℝ) := by
  induction y using Finsupp.induction_linear with
  | zero => simp [DivisorWithCoeffs.coeff_apply]
  | add a b ha hb =>
    simp only [map_add, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply] at ha hb ⊢
    rw [ha, hb]
    push_cast
    rfl
  | single L r =>
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.linearCombination_single]
    left
    exact (Rat.cast_intCast ((v L) E)).symm

/-- A linear map factors through `S` once it kills the kernel of `S` (over a field). -/
private theorem exists_comp_eq_of_ker_le {K V V' V'' : Type*} [Field K] [AddCommGroup V]
    [AddCommGroup V'] [AddCommGroup V''] [Module K V] [Module K V'] [Module K V'']
    (S : V →ₗ[K] V') (T : V →ₗ[K] V'') (h : LinearMap.ker S ≤ LinearMap.ker T) :
    ∃ β : V' →ₗ[K] V'', ∀ x, β (S x) = T x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker S).liftQ T h).comp S.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun x => ?_⟩
  have := LinearMap.congr_fun hg ⟨S x, LinearMap.mem_range_self S x⟩
  simpa [LinearMap.quotKerEquivRange_symm_apply_image] using this

/-- A rational point of the real span of rational vectors lies in their rational span. -/
private theorem exists_rat_of_eq_sum_real {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : κ → ι → ℚ) (v : ι → ℚ) (t : κ → ℝ)
    (h : (fun i => (v i : ℝ)) = ∑ k, t k • fun i => (w k i : ℝ)) :
    ∃ s : κ → ℚ, v = ∑ k, s k • w k := by
  by_contra hne
  have hv : v ∉ Submodule.span ℚ (Set.range w) := by
    intro hmem
    obtain ⟨s, hs⟩ := Submodule.mem_span_range_iff_exists_fun ℚ |>.mp hmem
    exact hne ⟨s, hs.symm⟩
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hw : ∀ k, φ (w k) = 0 := fun k => by
    have := Submodule.mem_map_of_mem (f := φ)
      (Submodule.subset_span ⟨k, rfl⟩ : w k ∈ Submodule.span ℚ (Set.range w))
    rw [hmap] at this
    simpa using this
  apply hφ
  have hR : ((φ v : ℚ) : ℝ) = 0 := by
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    have hk : ∀ k, ∑ i, (w k i : ℝ) * (φ fun j => if i = j then 1 else 0 : ℚ) = 0 := fun k => by
      have := hw k
      rw [LinearMap.pi_apply_eq_sum_univ φ (w k)] at this
      simpa [smul_eq_mul] using congrArg (fun q : ℚ => (q : ℝ)) this
    simp only [smul_eq_mul, Rat.cast_sum, Rat.cast_mul]
    have hvi : ∀ i, (v i : ℝ) = ∑ k, t k * (w k i : ℝ) := fun i => by
      have := congrFun h i
      simpa [Finset.sum_apply] using this
    simp_rw [hvi, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp_rw [mul_assoc, ← Finset.mul_sum, hk k, mul_zero]
  exact_mod_cast hR

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- Real presentations `∑ r_L L` of `ℝ`-divisors by Cartier divisors, as `ℝ`-divisors. -/
private noncomputable def presDiv (X : Scheme.{u}) [IsLocallyNoetherian X] [IsNormal X] :
    (↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ) →ₗ[ℝ] RDivisor X :=
  Finsupp.linearCombination ℝ fun L => Divisor.toRDivisor (L : Divisor X)

variable [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y] [CompactSpace Y]

/-- The pull-back `∑ r_L f^*L` of a real presentation. -/
private noncomputable def presPull (f : Y ⟶ X) [IsDominant f] :
    (↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ) →ₗ[ℝ] RDivisor Y :=
  Finsupp.linearCombination ℝ fun L => Divisor.toRDivisor (cartierPullbackHom f L)

private theorem presPull_eq (f : Y ⟶ X) [IsDominant f]
    {y y' : ↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ} (h : presDiv X y = presDiv X y') :
    presPull f y = presPull f y' := by
  have h' : toTensor _ y = toTensor _ y' := rDivisorTensorMap_cartierSubgroup_injective (by
    rwa [rDivisorTensorMap_toTensor, rDivisorTensorMap_toTensor])
  have e : ∀ z, presPull f z = rDivisorTensorMap (cartierPullbackHom f) (toTensor _ z) :=
    fun z => (rDivisorTensorMap_toTensor _ z).symm
  rw [e, e, h']

private theorem eq_presPull_of_isRCartierPullback (f : Y ⟶ X) [IsDominant f] {D : RDivisor X}
    {G : RDivisor Y} (hG : IsRCartierPullback f D G)
    {y : ↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ} (hy : presDiv X y = D) :
    G = presPull f y := by
  obtain ⟨m, r, L, hD, rfl⟩ := hG.eq_rDivisorTensorMap f
  let y' : ↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ := ∑ j, Finsupp.single (L j) (r j)
  have ht : toTensor _ y' = ∑ j, L j ⊗ₜ r j := by
    simp [y', toTensor, map_sum]
  have h1 : presDiv X y' = D := by
    simp [y', presDiv, hD, map_sum, Finsupp.linearCombination_single]
  rw [← ht, rDivisorTensorMap_toTensor]
  exact presPull_eq f (h1.trans hy.symm)

end Pullback

/-- The real coefficients of a rational presentation. -/
private noncomputable abbrev castR (G : Type*) : (G →₀ ℚ) →+ (G →₀ ℝ) :=
  Finsupp.mapRange.addMonoidHom (Rat.castHom ℝ).toAddMonoidHom

private theorem exists_linearCombination_eq_of_isCartierCombination {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {Q : QDivisor X} (hQ : IsCartierCombination Q) :
    ∃ y : ↥(Divisor.cartierSubgroup (X := X)) →₀ ℚ,
      Finsupp.linearCombination ℚ
        (fun L : ↥(Divisor.cartierSubgroup (X := X)) => Divisor.toQDivisor (L : Divisor X)) y =
        Q := by
  obtain ⟨m, r, L, hL, rfl⟩ := hQ
  refine ⟨∑ j, Finsupp.single ⟨L j, hL j⟩ (r j), ?_⟩
  simp only [map_sum, Finsupp.linearCombination_single]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

private theorem toRDivisor_toQDivisor_add_sum_single {X : Scheme.{u}} (K : Divisor X)
    {ι : Type*} [Fintype ι] (P : ι → MMP.Mori.PrimeDivisor X) (a : ι → ℚ) :
    QDivisor.toRDivisor (Divisor.toQDivisor K + ∑ i, Finsupp.single (P i) (a i)) =
      Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (a i : ℝ) := by
  classical
  have e1 : ∀ (D : QDivisor X) E, QDivisor.toRDivisor D E = (D E : ℝ) := fun _ _ => rfl
  have e2 : ∀ (D : Divisor X) E, Divisor.toRDivisor D E = (D E : ℝ) := fun _ _ => rfl
  have e3 : ∀ (D : Divisor X) E, Divisor.toQDivisor D E = (D E : ℚ) := fun _ _ => rfl
  refine DivisorWithCoeffs.ext' fun E => ?_
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Finset.sum_apply, e1, e2, e3]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

private theorem toRDivisor_add_sum_smul_single_one {X : Scheme.{u}} (K : Divisor X)
    {ι : Type*} [Fintype ι] (P : ι → MMP.Mori.PrimeDivisor X) (c : ι → ℝ) :
    QDivisor.toRDivisor (Divisor.toQDivisor K) +
      ∑ i, c i • QDivisor.toRDivisor (Finsupp.single (P i) 1) =
      Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (c i) := by
  classical
  have e1 : ∀ (D : QDivisor X) E, QDivisor.toRDivisor D E = (D E : ℝ) := fun _ _ => rfl
  have e2 : ∀ (D : Divisor X) E, Divisor.toRDivisor D E = (D E : ℝ) := fun _ _ => rfl
  have e3 : ∀ (D : Divisor X) E, Divisor.toQDivisor D E = (D E : ℚ) := fun _ _ => rfl
  refine DivisorWithCoeffs.ext' fun E => ?_
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Finset.sum_apply, e1, e2, e3]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

private theorem add_sum_mul_eq_sub_add_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ℝ)
    (b β : ι → ℝ) (t : κ → ℝ) (w : κ → ι → ℝ) (γ : κ → ℝ) (h : ∀ k, γ k = ∑ i, w k i * β i) :
    a + ∑ k, t k * γ k = a - ∑ i, b i * β i + ∑ i, β i * (b i + ∑ j, t j * w j i) := by
  simp only [h, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := ι))]
  have hs : ∑ i, β i * b i = ∑ i, b i * β i := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hu : ∑ k, ∑ i, t k * (w k i * β i) = ∑ k, ∑ i, β i * (t k * w k i) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, hu]
  ring

/-- Along a dominant `f`, once `D_c = K + ∑ cᵢ Pᵢ` is `ℚ`-Cartier at every rational point of
`b⁰ + span_ℚ {w_j}`, the coefficients of every pull-back `f^*D_c` at the real points
`c = b⁰ + ∑ tⱼ wⱼ` are rational affine functions of `c`. -/
private theorem exists_coeff_isRCartierPullback_affine {X W : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W] [CompactSpace W]
    (f : W ⟶ X) [IsDominant f] (K : Divisor X) {ι : Type*} [Fintype ι]
    (P : ι → MMP.Mori.PrimeDivisor X) {p : ℕ} (b₀ : ι → ℚ) (w : Fin p → ι → ℚ)
    (hQ : ∀ s : Fin p → ℚ, IsCartierCombination
      (Divisor.toQDivisor K + ∑ i, Finsupp.single (P i) ((b₀ + ∑ j, s j • w j) i))) :
    ∃ (α : MMP.Mori.PrimeDivisor W → ℚ) (β : MMP.Mori.PrimeDivisor W → ι → ℚ),
      ∀ (t : Fin p → ℝ) (G : RDivisor W), IsRCartierPullback f (Divisor.toRDivisor K +
          ∑ i, Finsupp.single (P i) ((b₀ i : ℝ) + ∑ j, t j * (w j i : ℝ))) G →
        ∀ E, G.coeff E = α E + ∑ i, (β E i : ℝ) * ((b₀ i : ℝ) + ∑ j, t j * (w j i : ℝ)) := by
  classical
  let ℓ : (ι → ℝ) →ₗ[ℝ] RDivisor X :=
    Fintype.linearCombination ℝ fun i => Finsupp.single (P i) (1 : ℝ)
  have hℓ : ∀ c : ι → ℝ, ∑ i, Finsupp.single (P i) (c i) = ℓ c := fun c => by
    simp [ℓ, Fintype.linearCombination_apply]
  let b₀R : ι → ℝ := fun i => (b₀ i : ℝ)
  let wR : Fin p → ι → ℝ := fun j i => (w j i : ℝ)
  obtain ⟨y₀, hy₀⟩ := exists_linearCombination_eq_of_isCartierCombination (hQ 0)
  choose y hy using fun k : Fin p =>
    exists_linearCombination_eq_of_isCartierCombination (hQ (Pi.single k 1))
  have hcast : ∀ z : ↥(Divisor.cartierSubgroup (X := X)) →₀ ℚ,
      presDiv X (castR _ z) = QDivisor.toRDivisor (Finsupp.linearCombination ℚ
        (fun L : ↥(Divisor.cartierSubgroup (X := X)) => Divisor.toQDivisor (L : Divisor X)) z) :=
    fun z => DivisorWithCoeffs.ext' fun E =>
      coeff_linearCombination_mapRange (fun L : ↥(Divisor.cartierSubgroup (X := X)) =>
        (L : Divisor X)) z E
  have hΦ0 : presDiv X (castR _ y₀) = Divisor.toRDivisor K + ℓ b₀R := by
    rw [hcast, hy₀, toRDivisor_toQDivisor_add_sum_single, hℓ]
    congr 2
    funext i
    simp [b₀R]
  have hd : ∀ k, presDiv X (castR _ (y k)) - presDiv X (castR _ y₀) = ℓ (wR k) := by
    intro k
    have hΦk : presDiv X (castR _ (y k)) = Divisor.toRDivisor K + ℓ (b₀R + wR k) := by
      rw [hcast, hy k, toRDivisor_toQDivisor_add_sum_single, hℓ]
      congr 2
      funext i
      simp [b₀R, wR, Pi.single_apply]
    rw [hΦk, hΦ0, map_add]
    abel
  let yt : (Fin p → ℝ) → (↥(Divisor.cartierSubgroup (X := X)) →₀ ℝ) := fun t =>
    castR _ y₀ + ∑ k, t k • (castR _ (y k) - castR _ y₀)
  have hΦt : ∀ t, presDiv X (yt t) = Divisor.toRDivisor K + ℓ (b₀R + ∑ k, t k • wR k) := by
    intro t
    simp only [yt, map_add, map_sum, map_smul, map_sub, hd]
    rw [hΦ0]
    abel
  let A : (↥(Divisor.cartierSubgroup (X := X)) →₀ ℚ) → MMP.Mori.PrimeDivisor W → ℚ :=
    fun z E => (Finsupp.linearCombination ℚ (fun L : ↥(Divisor.cartierSubgroup (X := X)) =>
      Divisor.toQDivisor (cartierPullbackHom f L)) z).coeff E
  let γ : Fin p → MMP.Mori.PrimeDivisor W → ℚ := fun k E => A (y k) E - A y₀ E
  have hcoeff : ∀ t E, (presPull f (yt t)).coeff E = A y₀ E + ∑ k, t k * γ k E := by
    intro t E
    have hc : ∀ z, (presPull f (castR _ z)).coeff E = (A z E : ℝ) :=
      fun z => coeff_linearCombination_mapRange (fun L => cartierPullbackHom f L) z E
    simp only [yt, map_add, map_sum, map_smul, map_sub, DivisorWithCoeffs.coeff_apply,
      Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
      smul_eq_mul] at hc ⊢
    simp only [hc, γ, Rat.cast_sub]
  have hker : ∀ E, LinearMap.ker (Fintype.linearCombination ℚ w) ≤
      LinearMap.ker (Fintype.linearCombination ℚ fun k => γ k E) := by
    intro E s hs
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hs ⊢
    have hsR : ∑ k, (s k : ℝ) • wR k = 0 := by
      funext i
      simpa [Finset.sum_apply, wR] using congr_arg (fun v : ι → ℚ => (v i : ℝ)) hs
    have := congrArg (fun G : RDivisor W => G.coeff E)
      (presPull_eq f (y := yt fun k => (s k : ℝ)) (y' := yt 0) (by rw [hΦt, hΦt, hsR]; simp))
    simp only [hcoeff, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
      add_eq_left] at this
    simp only [smul_eq_mul]
    exact_mod_cast this
  choose β hβ using fun E => exists_comp_eq_of_ker_le _ _ (hker E)
  let e : ι → ι → ℚ := fun i j => if i = j then 1 else 0
  refine ⟨fun E => A y₀ E - ∑ i, b₀ i * β E (e i), fun E i => β E (e i), ?_⟩
  intro t G hG E
  have hfun : (fun i => (b₀ i : ℝ) + ∑ j, t j * (w j i : ℝ)) = b₀R + ∑ k, t k • wR k := by
    funext i
    simp [b₀R, wR, Finset.sum_apply]
  rw [hℓ, hfun] at hG
  rw [eq_presPull_of_isRCartierPullback f hG (hΦt t), hcoeff]
  have hγβ : ∀ k, (γ k E : ℝ) = ∑ i, (w k i : ℝ) * (β E (e i) : ℝ) := by
    intro k
    have := hβ E (Pi.single k 1)
    rw [Fintype.linearCombination_apply_single, Fintype.linearCombination_apply_single,
      one_smul, one_smul, LinearMap.pi_apply_eq_sum_univ] at this
    rw [← this]
    push_cast
    simp [smul_eq_mul, e]
  push_cast
  exact add_sum_mul_eq_sub_add_sum _ (fun i => (b₀ i : ℝ)) (fun i => (β E (e i) : ℝ)) t
    (fun j i => (w j i : ℝ)) (fun k => (γ k E : ℝ)) hγβ
/-- Let `X` be a normal variety with canonical divisor `K`, let `P i` (`i ∈ ι`, finite) be prime
divisors on `X`, and suppose `K + ∑ bᵢ Pᵢ` is `ℝ`-Cartier. Then there is an affine subspace
`V = b⁰ + span_ℝ {w₁, …, w_p}` of `ℝ^ι` with `b⁰, wⱼ ∈ ℚ^ι` and `b ∈ V` such that
* `D_c = K + ∑ cᵢ Pᵢ` is `ℝ`-Cartier for every `c ∈ V`;
* `K + ∑ cᵢ Pᵢ` is `ℚ`-Cartier for every rational `c ∈ V`;
* for every projective birational morphism `f : W ⟶ X` from a normal integral scheme, there are
  rational numbers `α_E`, `β_{E,i}` (for prime divisors `E` of `W`) with
  `coeff_E (f^*D_c) = α_E + ∑ᵢ β_{E,i} cᵢ` for all `c ∈ V`. -/
@[mmp "lem_fourfold_real_adjoint_rational_cartier_locus"]
public theorem exists_rat_affineSubspace_isCartierCombination_and_coeff_pullback_affine
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {ι : Type*} [Fintype ι] (P : ι → Mori.PrimeDivisor X)
    (b : ι → ℝ)
    (hb : IsCartierCombination (Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (b i))) :
    ∃ (V : AffineSubspace ℝ (ι → ℝ)) (b₀ : ι → ℚ) (p : ℕ) (w : Fin p → ι → ℚ),
      V = AffineSubspace.mk' (fun i => (b₀ i : ℝ))
        (Submodule.span ℝ (Set.range fun j i => (w j i : ℝ))) ∧
      b ∈ V ∧
      (∀ c ∈ V, IsCartierCombination (Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (c i))) ∧
      (∀ c : ι → ℚ, (fun i => (c i : ℝ)) ∈ V →
        IsCartierCombination (Divisor.toQDivisor K + ∑ i, Finsupp.single (P i) (c i))) ∧
      ∀ (W : Scheme.{u}) [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W] (f : W ⟶ X),
        IsProjective f → IsBirationalMorphism f →
        ∃ (α : Mori.PrimeDivisor W → ℚ) (β : Mori.PrimeDivisor W → ι → ℚ),
          ∀ c ∈ V, ∀ G : RDivisor W,
            IsRCartierPullback f (Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (c i)) G →
            ∀ E : Mori.PrimeDivisor W, G.coeff E = α E + ∑ i, (β E i : ℝ) * c i := by
  classical
  obtain ⟨b₀, p, w, hiff, hQ⟩ := exists_rat_affineSubspace_isCartierCombination
    (Divisor.toQDivisor K) (fun i => Finsupp.single (P i) 1)
    ⟨b, by rwa [toRDivisor_add_sum_smul_single_one]⟩
  have hQ' : ∀ s : Fin p → ℚ, IsCartierCombination
      (Divisor.toQDivisor K + ∑ i, Finsupp.single (P i) ((b₀ + ∑ j, s j • w j) i)) :=
    fun s => by simpa [Finsupp.smul_single_one] using hQ s
  have hmemV : ∀ c, c ∈ AffineSubspace.mk' (fun i => (b₀ i : ℝ))
      (Submodule.span ℝ (Set.range fun j i => (w j i : ℝ))) ↔
      ∃ t : Fin p → ℝ, c = (fun i => (b₀ i : ℝ)) + ∑ j, t j • fun i => (w j i : ℝ) := by
    intro c
    rw [AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht, vsub_eq_sub]; abel⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp⟩
  have hV : ∀ c, c ∈ AffineSubspace.mk' (fun i => (b₀ i : ℝ))
      (Submodule.span ℝ (Set.range fun j i => (w j i : ℝ))) ↔
      IsCartierCombination (Divisor.toRDivisor K + ∑ i, Finsupp.single (P i) (c i)) := by
    intro c
    rw [hmemV, ← toRDivisor_add_sum_smul_single_one]
    exact (hiff c).symm
  refine ⟨_, b₀, p, w, rfl, (hV b).2 hb, fun c hc => (hV c).1 hc, ?_, ?_⟩
  · intro c hc
    obtain ⟨t, ht⟩ := (hmemV _).1 hc
    obtain ⟨s, hs⟩ := exists_rat_of_eq_sum_real w (c - b₀) t (by
      funext i
      have := congrFun ht i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Pi.sub_apply, Rat.cast_sub, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      linarith)
    have hc' : b₀ + ∑ j, s j • w j = c := by rw [← hs]; abel
    simpa only [hc'] using hQ' s
  · intro W _ _ _ f hproj hbir
    have : IsDominant f := hbir.isDominant
    have : QuasiCompact sX := hX.1.toQuasiCompact
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have : IsProper f := hproj.isProper
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
    obtain ⟨α, β, h⟩ := exists_coeff_isRCartierPullback_affine f K P b₀ w hQ'
    refine ⟨α, β, fun c hc G hG E => ?_⟩
    obtain ⟨t, rfl⟩ := (hmemV c).1 hc
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hG ⊢
    exact h t G hG E

end RationalCartierLocus

/-! ### A small morphism to an affine base moves a prime divisor -/

section MobilePrime

section Helpers

variable {X Y : Scheme.{u}}

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If `Ex(f)` has codimension at least two, the images of the generic points of two distinct
prime divisors are not related by specialization. -/
private theorem not_map_genericPoint_specializes {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) {Q S : MMP.Mori.PrimeDivisor X}
    (hQS : Q ≠ S) : ¬ f Q.genericPoint ⤳ f S.genericPoint := by
  intro h
  have hmem : ∀ P : MMP.Mori.PrimeDivisor X, f P.genericPoint ∈ biregularLocus f := fun P =>
    not_not.mp fun hP => by
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (x := P.genericPoint) hP
      rw [P.coheight_genericPoint] at this
      exact absurd this (by decide)
  have hsp : Q.genericPoint ⤳ S.genericPoint :=
    specializes_of_map_specializes (hmem Q) (hmem S) h
  apply hQS
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  by_contra hne
  have hlt : S.genericPoint < Q.genericPoint :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun h' =>
      hne (hsp.antisymm (Scheme.le_iff_specializes.mp h')).eq
  have hstep := Order.coheight_add_one_le hlt
  rw [Q.coheight_genericPoint, S.coheight_genericPoint] at hstep
  exact absurd hstep (by decide)

/-- On an affine target, a point `f y` that is not a specialization of `f x` is separated from it
by a global function: its pull-back is invertible at `y` and not at `x`. -/
private theorem exists_appTop_mem_basicOpen [IsAffine Y] (f : X ⟶ Y) {x y : X}
    (h : ¬ f x ⤳ f y) :
    ∃ g : Γ(X, ⊤), y ∈ X.basicOpen g ∧ x ∉ X.basicOpen g := by
  let V : Y.Opens := ⟨(closure {f x})ᶜ, isClosed_closure.isOpen_compl⟩
  have hyV : f y ∈ V := fun hy => h (specializes_iff_mem_closure.mpr hy)
  obtain ⟨g, hgV, hyg⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨f y, hyV⟩ trivial
  refine ⟨f.appTop g, ?_, ?_⟩
  · rwa [← Scheme.preimage_basicOpen_top]
  · rw [← Scheme.preimage_basicOpen_top]
    exact fun hx => hgV hx (subset_closure rfl)

end Helpers

section Moving

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]

/-- A global function invertible at the generic point of a prime divisor `S`, regarded as a unit
of `K(X)`, has nonnegative order everywhere, order zero along `S`, and positive order along every
prime divisor at whose generic point it is not invertible. -/
private theorem exists_unit_of_mem_basicOpen (S Q : MMP.Mori.PrimeDivisor X) (g : Γ(X, ⊤))
    (hS : S.genericPoint ∈ X.basicOpen g) (hQ : Q.genericPoint ∉ X.basicOpen g) :
    ∃ w : (RationalFunctions X)ˣ, (∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ P.ord w) ∧
      S.ord w = 0 ∧ 1 ≤ Q.ord w := by
  have ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ (⊤ : X.Opens)),
      (X.presheaf.germ ⊤ _ hZ).hom g ≠ 0 := by
    intro Z hZ
    have hmem : S.genericPoint ∈ Z.1 := by
      have h := Z.2
      simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
      rw [h]
      trivial
    have hZS : componentGenericPoint X Z ∈ X.basicOpen g :=
      ((isGenericPoint_componentGenericPoint X Z).specializes hmem).mem_open
        (X.basicOpen g).isOpen hS
    exact ((Scheme.mem_basicOpen _ g _ hZ).mp hZS).ne_zero
  refine ⟨MMP.Threefold.Resolution.sectionUnit g ha,
    fun P => MMP.Threefold.Resolution.ord_sectionUnit_nonneg g ha P trivial,
    MMP.Threefold.Resolution.ord_sectionUnit_eq_zero g ha S trivial
      ((Scheme.mem_basicOpen _ g _ trivial).mp hS),
    MMP.Threefold.Resolution.one_le_ord_sectionUnit g ha Q trivial
      (fun hu => hQ ((Scheme.mem_basicOpen _ g _ trivial).mpr hu))⟩

/-- If every prime divisor `Q ≠ S` is separated from `S` by a global function, then every divisor
`D` has a rational function `φ` with `D + div φ ≥ 0` and `ord_S φ = -coeff_S D`. -/
private theorem exists_add_ord_nonneg_of_separated (S : MMP.Mori.PrimeDivisor X)
    (hsep : ∀ Q : MMP.Mori.PrimeDivisor X, Q ≠ S →
      ∃ g : Γ(X, ⊤), S.genericPoint ∈ X.basicOpen g ∧ Q.genericPoint ∉ X.basicOpen g)
    (D : Divisor X) :
    ∃ φ : (RationalFunctions X)ˣ, (∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ D.coeff P + P.ord φ) ∧
      S.ord φ = -D.coeff S := by
  classical
  have hw : ∀ Q : MMP.Mori.PrimeDivisor X, ∃ w : (RationalFunctions X)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ P.ord w) ∧ (Q ≠ S → S.ord w = 0 ∧ 1 ≤ Q.ord w) := by
    intro Q
    by_cases hQ : Q = S
    · exact ⟨1, fun P => by simp, absurd hQ⟩
    · obtain ⟨g, hgS, hgQ⟩ := hsep Q hQ
      obtain ⟨w, h0, hS, h1⟩ := exists_unit_of_mem_basicOpen S Q g hgS hgQ
      exact ⟨w, h0, fun _ => ⟨hS, h1⟩⟩
  choose w hw0 hw1 using hw
  obtain ⟨t, ht⟩ := MMP.Flips.exists_primeDivisor_ord_eq S (-D.coeff S)
  let B : Finset (MMP.Mori.PrimeDivisor X) :=
    (D.support ∪ (principalDivisor t).support).erase S
  let n : MMP.Mori.PrimeDivisor X → ℕ := fun Q => (D.coeff Q + Q.ord t).natAbs
  have hord (P : MMP.Mori.PrimeDivisor X) :
      P.ord (∏ Q ∈ B, w Q ^ n Q) = ∑ Q ∈ B, (n Q : ℤ) * P.ord (w Q) := by
    simp [PrimeDivisor.ord, map_prod, toAdd_prod]
  refine ⟨t * ∏ Q ∈ B, w Q ^ n Q, fun P => ?_, ?_⟩
  · have hsum : ∀ Q ∈ B, 0 ≤ (n Q : ℤ) * P.ord (w Q) := fun Q _ =>
      mul_nonneg (Int.natCast_nonneg _) (hw0 Q P)
    rw [PrimeDivisor.ord_mul, hord, ← add_assoc]
    by_cases hP : P ∈ B
    · have hle := Finset.single_le_sum hsum hP
      have h1 := (hw1 P (Finset.ne_of_mem_erase hP)).2
      have hn : -(D.coeff P + P.ord t) ≤ n P := by
        simpa [n] using neg_le_abs (D.coeff P + P.ord t)
      nlinarith
    · have hP0 : D.coeff P + P.ord t = 0 := by
        by_cases hPS : P = S
        · rw [hPS, ht, add_neg_cancel]
        · simp only [B, Finset.mem_erase, Finset.mem_union, Finsupp.mem_support_iff, not_and,
            not_or, not_not] at hP
          obtain ⟨hD, ht0⟩ := hP hPS
          rw [show D.coeff P = 0 from hD, show P.ord t = 0 from ht0, add_zero]
      rw [hP0, zero_add]
      exact Finset.sum_nonneg hsum
  · rw [PrimeDivisor.ord_mul, hord, ht, Finset.sum_eq_zero fun Q hQ => by
      rw [(hw1 Q (Finset.ne_of_mem_erase hQ)).1, mul_zero], add_zero]

/-- Under the separation hypothesis, every divisor is linearly equivalent to an effective
divisor with coefficient zero at `S`. -/
private theorem exists_linearlyEquivalent_of_separated (S : MMP.Mori.PrimeDivisor X)
    (hsep : ∀ Q : MMP.Mori.PrimeDivisor X, Q ≠ S →
      ∃ g : Γ(X, ⊤), S.genericPoint ∈ X.basicOpen g ∧ Q.genericPoint ∉ X.basicOpen g)
    (D : Divisor X) :
    ∃ D' : Divisor X, 0 ≤ D' ∧ D'.LinearlyEquivalent D ∧ D'.coeff S = 0 := by
  obtain ⟨φ, hφ, hS⟩ := exists_add_ord_nonneg_of_separated S hsep D
  refine ⟨D + principalDivisor φ, hφ, ⟨φ, add_sub_cancel_left _ _⟩, ?_⟩
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, hS, add_neg_cancel]

end Moving

variable {k : Type u} [Field k] {X Z : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
  [IsNormal X]
  {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}

/-- Over an affine base, a small morphism makes every divisor linearly equivalent to an effective
divisor with coefficient zero at a given prime divisor `S`. -/
public theorem IsSmallMorphism.exists_nonneg_linearlyEquivalent_coeff_eq_zero
    (hf : IsSmallMorphism sX sZ f) [IsAffine Z] (S : MMP.Mori.PrimeDivisor X) (D : Divisor X) :
    ∃ D' : Divisor X, 0 ≤ D' ∧ D'.LinearlyEquivalent D ∧ D'.coeff S = 0 := by
  have : IsIntegral X := hf.isNormalVariety_source.1.toIsIntegral
  exact exists_linearlyEquivalent_of_separated S (fun Q hQ => exists_appTop_mem_basicOpen f
    (not_map_genericPoint_specializes hf.two_le_codimension hQ)) D

/-- Let `f : X ⟶ Z` be a small projective birational morphism of normal varieties with `Z`
affine, and let `S` be a prime divisor on `X`.
1. There is an effective divisor `S' ∼ S` with coefficient zero at `S`.
2. If `L` is a `ℚ`-Cartier `ℚ`-divisor with coefficient zero at `S`, then every Cartier divisor
   `D` with `D = m • L` for some `m : ℤ` is linearly equivalent to an effective divisor with
   coefficient zero at `S`. -/
@[mmp "lem_fourfold_small_affine_mobile_prime"]
public theorem IsSmallMorphism.exists_linearlyEquivalent_coeff_eq_zero
    (hf : IsSmallMorphism sX sZ f) (hproj : IsProjectiveMorphism f) [IsAffine Z]
    (S : MMP.Mori.PrimeDivisor X) :
    (∃ S' : Divisor X, 0 ≤ S' ∧ S'.LinearlyEquivalent (Finsupp.single S 1) ∧ S'.coeff S = 0) ∧
    ∀ L : QDivisor X, L.IsQCartier → L.coeff S = 0 →
      ∀ (m : ℤ) (D : Divisor X), D.IsCartier → Divisor.toQDivisor D = m • L →
        ∃ D' : Divisor X, 0 ≤ D' ∧ D'.LinearlyEquivalent D ∧ D'.coeff S = 0 :=
  ⟨hf.exists_nonneg_linearlyEquivalent_coeff_eq_zero S _,
    fun _ _ _ _ D _ _ => hf.exists_nonneg_linearlyEquivalent_coeff_eq_zero S D⟩

end MobilePrime

/-! ### An ample decomposition avoiding a prime divisor -/

section AmpleDecomposition

open MMP.Threefold.Bridges

/-- Over an affine base, a projective morphism from a normal integral scheme carries an
`f`-ample Cartier divisor whose divisorial sheaf is ample. -/
private theorem exists_isRelativelyAmple_of_isProjectiveMorphism
    {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]
    {f : X ⟶ Z} (hproj : IsProjectiveMorphism f) [IsAffine Z] :
    ∃ (H : Divisor X) (hH : H.IsCartier), H.IsRelativelyAmple f hH ∧
      ∀ [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf],
        Stacks.Ample.IsAmple X H.divisorialSheaf := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have := Stacks.Ample.isInvertibleModule_unit Z
  obtain ⟨L, hLinv, hL⟩ := AlgebraicGeometry.exists_isAmple_of_isQuasiProjective f
    (Stacks.Ample.unitModule Z) (Stacks.Ample.isAmple_unitModule_of_isAffine Z)
    (AlgebraicGeometry.isQuasiProjective_of_isHQuasiProjective f hproj.isHQuasiProjective)
  obtain ⟨I, hI, -, -, n, hn, ⟨e⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor I hI
  have := hHc.isInvertibleModule_divisorialSheaf
  have hHamp : Stacks.Ample.IsAmple X H.divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ (e ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)
  exact ⟨H, hHc,
    MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf f hHc hHamp,
    fun [_] => by convert hHamp⟩

private theorem exists_coefficientPoint_mem_of_dense {k : Type u} [Field k] [Infinite k] {N : ℕ}
    (U V : (coefficientSpace k N).Opens) (hU : Dense (U : Set (coefficientSpace k N)))
    (hV : Dense (V : Set (coefficientSpace k N))) :
    ∃ c : Fin (N + 1) → k, coefficientPoint c ∈ U ∧
      coefficientPoint c ∈ V := by
  have hW : Dense ((U : Set (coefficientSpace k N)) ∩ (V : Set _)) :=
    Dense.inter_of_isOpen_left hU hV U.isOpen
  obtain ⟨p, hp⟩ := hW.nonempty
  obtain ⟨_, ⟨Q, rfl⟩, hpQ, hQW⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := MvPolynomial (Fin (N + 1)) k)).exists_subset_of_mem_open hp (U.isOpen.inter V.isOpen)
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hpQ
    exact hpQ
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c Q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ0 (MvPolynomial.funext fun c => by simpa using h c)
  refine ⟨c, hQW ?_⟩
  change Q ∉ RingHom.ker (MvPolynomial.eval c)
  exact fun h0 => hc (RingHom.mem_ker.mp h0)

/-- For an ample invertible module `M` on a quasi-compact scheme and any `N`, some power
`M^{⊗n}` with `0 < n` and `N ≤ n` has finitely many global sections `s₀, …, s_K` whose
nonvanishing loci cover `X`. -/
public theorem exists_forall_exists_mem_nonvanishingLocus_of_isAmple {X : Scheme.{u}}
    [CompactSpace X] (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (hM : Stacks.Ample.IsAmple X M) (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ N ≤ n ∧
      ∃ (K : ℕ) (s : Fin (K + 1) → Γ(Stacks.Ample.tensorPowModule X M (n : ℤ), ⊤)), ∀ x : X,
        ∃ i, x ∈ Stacks.Ample.nonvanishingLocus
          (Stacks.Ample.tensorPowModule X M (n : ℤ)) (s i) := by
  classical
  have hx : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(Stacks.Ample.tensorPowModule X M (n : ℤ), ⊤),
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X M (n : ℤ)) s := by
    intro x
    obtain ⟨n, hn, s, -, hxs, -⟩ :=
      Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M hM
        (Set.finite_singleton x) ⊤ (by simp)
    exact ⟨n, hn, s, hxs rfl⟩
  choose n hn s hs using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X M (n x : ℤ)) (s x))
    (fun x => (Stacks.NonvanishingOpen.nonvanishingOpen X _ (s x)).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hs x⟩)
  set D : ℕ := (N + 1) * ∏ x ∈ t, n x
  have hD : 0 < D := Nat.mul_pos (Nat.succ_pos N)
    (Finset.prod_pos fun x _ => hn x)
  have hdvd : ∀ x ∈ t, n x ∣ D := fun x hx =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem n hx) _
  have hs' : ∀ x ∈ t, ∃ s' : Γ(Stacks.Ample.tensorPowModule X M (D : ℤ), ⊤),
      Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X M (D : ℤ)) s' =
        Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X M (n x : ℤ)) (s x) :=
      fun x hx =>
    Stacks.Ample.exists_tensorPow_nonvanishingLocus_eq_of_dvd M hD (hdvd x hx) (s x)
  choose! s' hs'eq using hs'
  let e := t.equivFin
  refine ⟨D, hD, le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_right _
    (Finset.prod_pos fun x _ => hn x)), t.card, fun i =>
      if h : (i : ℕ) < t.card then s' (e.symm ⟨i, h⟩) else 0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  refine ⟨⟨e ⟨y, hy⟩, Nat.lt_succ_of_lt (e ⟨y, hy⟩).2⟩, ?_⟩
  simpa [hs'eq y hy] using hxy

/-- In a domain, if `a = u ϖ^m` with `ϖ` irreducible and `(a)` is a radical ideal, then
`m ≤ 1`. -/
private theorem le_one_of_radical_span_eq {R : Type*} [CommRing R] [IsDomain R]
    {ϖ a : R} (hϖ : Irreducible ϖ) (u : Rˣ) (m : ℕ) (ha : a = u * ϖ ^ m)
    (hrad : (Ideal.span {a}).radical = Ideal.span {a}) : m ≤ 1 := by
  by_contra h
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hsq : Squarefree a :=
    (isRadical_iff_span_singleton.mpr (Ideal.radical_eq_iff.mp hrad)).squarefree ha0
  exact hϖ.not_isUnit (hsq ϖ (ha ▸ Dvd.dvd.mul_left
    (by simpa [← pow_two] using pow_dvd_pow ϖ (by omega : 2 ≤ m)) _))

/-- A principal radical ideal of the sections over an affine open stays radical in each stalk,
the stalk being a localization. -/
private theorem radical_span_germ_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (h : (Ideal.span {g}).radical = Ideal.span {g}) (y : X) (hy : y ∈ U) :
    (Ideal.span {(X.presheaf.germ U y hy).hom g}).radical =
      Ideal.span {(X.presheaf.germ U y hy).hom g} := by
  letI := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hU.isLocalization_stalk ⟨y, hy⟩
  have hmap := IsLocalization.map_radical (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk y) (Ideal.span {g})
  rw [h, Ideal.map_span, Set.image_singleton] at hmap
  exact hmap.symm

open MMP.Threefold.Resolution in
/-- If the germ of `a` at the generic point of a prime divisor `E` spans a radical ideal, then
`sectionUnit a ha` has order at most one along `E`. -/
private theorem ord_sectionUnit_le_one_of_radical {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {U : X.Opens} (a : Γ(X, U))
    (ha : ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U),
      (X.presheaf.germ U _ hZ).hom a ≠ 0) (E : MMP.Mori.PrimeDivisor X) (hE : E.genericPoint ∈ U)
    (hrad : (Ideal.span {(X.presheaf.germ U _ hE).hom a}).radical =
      Ideal.span {(X.presheaf.germ U _ hE).hom a}) :
    E.ord (sectionUnit a ha) ≤ 1 := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  set b := (X.presheaf.germ U _ hE).hom a
  have hb0 : b ≠ 0 := germ_genericPoint_ne_zero _ ha E hE
  obtain ⟨m, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hm := le_one_of_radical_span_eq hϖ u m hbu hrad
  have hval := E.valuation_component (sectionUnit a ha)
  rw [← toComponent_germ_eq_sectionUnit _ ha E hE] at hval
  change E.valuation (E.toComponent.hom b) = _ at hval
  rw [hbu, map_mul, map_mul, map_pow, map_pow, E.valuation_toComponent_of_isUnit u.isUnit,
    E.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul] at hval
  have := WithZero.exp_injective hval
  rw [← this]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hm

open MMP.Threefold.Resolution in
/-- **The divisor of a radical effective Cartier ideal.** On a normal integral Noetherian scheme,
an effective Cartier ideal sheaf `I` with `I.radical = I` is cut out by a divisor `D ≥ 0` with
`𝒪(D) ≅ 𝒪(I)`, all coefficients `0` or `1`, and coefficient `0` along every prime whose generic
point lies off the support of `I`. -/
private theorem exists_divisor_of_radical_eq_self {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hrad : I.radical = I) :
    ∃ D : Divisor X, Nonempty (D.divisorialSheaf ≅ Stacks.Divisors.invertibleSheaf' I) ∧
      (∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∉ I.supportSet → D.coeff P = 0) ∧
        ∀ P, D.coeff P = 0 ∨ D.coeff P = 1 := by
  classical
  have hex := fun x : X =>
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI x
  choose W hW hxW f hf hspan using hex
  have hgerm : ∀ x y (hy : y ∈ W x), IdealSheafData.stalk I y =
      Ideal.span {(X.presheaf.germ (W x) y hy).hom (f x)} := by
    intro x y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I y ⟨W x, hW x⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have ha : ∀ x (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ W x),
      (X.presheaf.germ (W x) _ hZ).hom (f x) ≠ 0 := fun x Z hZ =>
    nonZeroDivisors.ne_zero (Stacks.Divisors.germ_mem_nonZeroDivisors (hW x) (hf x) _ hZ)
  obtain ⟨D, hD⟩ := exists_divisor_isLocalEquation_sectionUnit W (fun x => ⟨x, hxW x⟩) f ha
    fun i j y hi hj =>
      Ideal.span_singleton_eq_span_singleton.1 ((hgerm i y hi).symm.trans (hgerm j y hj))
  have hcoeff : ∀ (E : MMP.Mori.PrimeDivisor X), D E = E.ord (sectionUnit (f E.genericPoint)
      (ha E.genericPoint)) := fun E =>
    hD E.genericPoint E ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      hxW _⟩
  have hD0 : 0 ≤ D := fun E => by
    change 0 ≤ D E
    rw [hcoeff]
    exact ord_sectionUnit_nonneg _ _ E (hxW _)
  have hle : ∀ E : MMP.Mori.PrimeDivisor X, D E ≤ 1 := fun E => by
    have hWrad : (Ideal.span {f E.genericPoint}).radical = Ideal.span {f E.genericPoint} := by
      have := congrArg (fun J : X.IdealSheafData => J.ideal ⟨W E.genericPoint, hW _⟩) hrad
      simp only [Scheme.IdealSheafData.radical_ideal] at this
      rwa [hspan] at this
    rw [hcoeff]
    exact ord_sectionUnit_le_one_of_radical _ _ E (hxW _)
      (radical_span_germ_eq (hW _) _ hWrad _ (hxW _))
  have hsupp : ∀ E : MMP.Mori.PrimeDivisor X, 0 < D E → E.genericPoint ∈ I.support := by
    intro E hE
    by_contra hnot
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support I _).2 hnot
    rw [hgerm E.genericPoint E.genericPoint (hxW _), Ideal.span_singleton_eq_top] at htop
    have := ord_sectionUnit_eq_zero _ (ha E.genericPoint) E (hxW _) htop
    rw [hcoeff] at hE
    omega
  refine ⟨D, nonempty_divisorialSheaf_iso_invertibleSheaf'_of_isLocalEquation I D hD0
      (fun x => ⟨W x, hxW x, _, hD x⟩) fun x => ⟨⟨W x, hW x⟩, hxW x, f x, _, hspan x, hD x,
        fun Z hZ => sectionUnit_apply _ _ Z hZ⟩, fun P hP => ?_, fun P => ?_⟩
  · by_contra hne
    exact hP (hsupp P (lt_of_le_of_ne (hD0 P) (Ne.symm hne)))
  · have h0 : 0 ≤ D P := hD0 P
    have := hle P
    change D P = 0 ∨ D P = 1
    omega

open MMP.Threefold.Resolution in
/-- **The divisor of a section with reduced zero scheme.** On a normal integral Noetherian scheme,
a nonzero section `σ` of an invertible sheaf `L` whose zero scheme is reduced has a divisor
`D ≥ 0` with `𝒪(D) ≅ L`, all coefficients `0` or `1`, and coefficient `0` along every prime
whose generic point lies in the nonvanishing locus of `σ`. -/
private theorem exists_divisor_of_isReduced_zeroScheme {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : ∃ x, x ∈ Stacks.Ample.nonvanishingLocus L σ)
    (hred : IsReduced (AlgebraicGeometry.zeroScheme X L σ).subscheme) :
    ∃ D : Divisor X, Nonempty (D.divisorialSheaf ≅ L) ∧
      (∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ Stacks.Ample.nonvanishingLocus L σ →
        D.coeff P = 0) ∧ ∀ P, D.coeff P = 0 ∨ D.coeff P = 1 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hσ
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    rw [Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop L σ).eval (Opposite.op ⊤) = σ :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ σ
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop L σ).eval (Opposite.op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop L σ) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hI' := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme L _ hne0'
  have hnv : Stacks.Ample.nonvanishingLocus L σ =
      (zeroScheme X L
        ((Stacks.SheafOfModules.sectionsOfTop L σ).eval (Opposite.op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _
        (Stacks.SheafOfModules.sectionsOfTop L σ)]
    rfl
  have eL := invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg
  rw [hevaltop] at hI' hnv eL
  set I := zeroScheme X L σ
  obtain ⟨D, ⟨eD⟩, h0, h01⟩ := exists_divisor_of_radical_eq_self I hI'
    (Stacks.Models.radical_eq_self_of_isReduced_subscheme I)
  exact ⟨D, ⟨eD ≪≫ eL.symm⟩, fun P hP => h0 P (by rw [hnv] at hP; exact hP), h01⟩

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
open Stacks.NonvanishingOpen (nonvanishingOpen) in
attribute [local instance] globalSectionsModule in
/-- **Reduced general members of `|nH|` avoiding finitely many primes.** On a normal variety in
characteristic zero with `𝒪(H)` ample, for `n ≫ 0` (and divisible enough) there is a divisor
`D ∼ nH` with all coefficients `0` or `1` and coefficient `0` along each prime of a finite set:
the zero divisor of a general section of the free system `|nH|` (Bertini). -/
private theorem exists_linearlyEquivalent_nsmul_reduced_of_isAmple
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    (H : Divisor X) (hH : H.IsCartier)
    (hamp : ∀ [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf],
      Stacks.Ample.IsAmple X H.divisorialSheaf)
    (N : ℕ) (T : Finset (MMP.Mori.PrimeDivisor X)) :
    ∃ n : ℕ, 0 < n ∧ N ≤ n ∧
      ∃ D : Divisor X, D.LinearlyEquivalent ((n : ℤ) • H) ∧
        (∀ P ∈ T, D.coeff P = 0) ∧ ∀ P, D.coeff P = 0 ∨ D.coeff P = 1 := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := hX.1.toLocallyOfFiniteType
  have : QuasiCompact (X ↘ Spec (.of k)) := hX.1.toQuasiCompact
  have := hH.isInvertibleModule_divisorialSheaf
  obtain ⟨n, hn, hNn, K, s, hs⟩ :=
    exists_forall_exists_mem_nonvanishingLocus_of_isAmple H.divisorialSheaf hamp N
  have hs' : ⨆ c : Fin (K + 1) → k,
      nonvanishingOpen X (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ))
        (systemSection s c) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := hs x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨Pi.single i 1, ?_⟩
    have : systemSection s (Pi.single i (1 : k)) = s i := by
      simp [systemSection_apply, Pi.single_apply]
    rwa [this]
  obtain ⟨⟨U, hU, hUred⟩, -⟩ := exists_dense_open_isReduced_zeroScheme s hs'
  obtain ⟨⟨V, hV, hVav⟩, -⟩ :=
    exists_dense_open_inter_nonvanishingOpen_nonempty hX.1 s hs'
      (ι := ↥(insert (genericPoint X) ((fun P : MMP.Mori.PrimeDivisor X => P.genericPoint) '' T)))
      (fun P => closure {P.1}) (fun _ => isClosed_closure)
      (fun _ => isIrreducible_singleton.closure)
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ)) :=
    (inferInstance : Stacks.Ample.IsInvertibleModule X _)
  obtain ⟨c, hcU, hcV⟩ := exists_coefficientPoint_mem_of_dense U V hU hV
  set σ := systemSection s c
  have hmem : ∀ x ∈ insert (genericPoint X)
      ((fun P : MMP.Mori.PrimeDivisor X => P.genericPoint) '' T),
      x ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule X H.divisorialSheaf (n : ℤ)) σ := by
    intro x hx
    obtain ⟨y, hy1, hy2⟩ := hVav c hcV ⟨x, hx⟩
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hy1 _ (nonvanishingOpen X _ σ).2 hy2
    rwa [Set.mem_singleton_iff.1 hz2] at hz1
  obtain ⟨D, ⟨eD⟩, hDT, hD01⟩ := exists_divisor_of_isReduced_zeroScheme _ σ
    ⟨_, hmem _ (Set.mem_insert _ _)⟩ (hUred c hcU)
  obtain ⟨e⟩ := hH.nonempty_tensorPowModule_iso_divisorialSheaf_zsmul n
  refine ⟨n, hn, hNn, D, MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (eD ≪≫ e), fun P hP => hDT P (hmem _ (Set.mem_insert_of_mem _ ⟨P, hP, rfl⟩)),
    hD01⟩

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}

/-- Let `f : X ⟶ Z` be a small projective birational morphism of normal varieties over an
algebraically closed field of characteristic zero, with `Z` affine and `X` `ℚ`-factorial, and
let `S` be a prime divisor on `X`. If `B ≥ 0` is a `ℚ`-divisor with coefficient zero at `S`,
there are an `f`-ample `ℚ`-divisor `A` and a `ℚ`-divisor `B₀ ≥ 0` with coefficient zero at `S`
such that `B ∼_ℚ A₀ + B₀` for every `A₀ ∼_ℚ A`. Moreover, for every `N : ℕ` and every finite
set `T` of prime divisors there are `m ≥ N` and `A₀ ∼_ℚ A` whose coefficients all lie in
`{0, 1/m}` and vanish at `S` and along `T`. -/
@[mmp "lem_fourfold_small_affine_ample_decomposition"]
public theorem IsSmallMorphism.exists_qLinearlyEquivalent_add_of_isQFactorial
    (hf : IsSmallMorphism sX sZ f) (hproj : IsProjectiveMorphism f) [IsAffine Z]
    (hQ : IsQFactorial sX) (S : MMP.Mori.PrimeDivisor X) (B : QDivisor X) (hB : 0 ≤ B)
    (_hBS : B.coeff S = 0) :
    ∃ A B₀ : QDivisor X, A.HasRelativelyAmpleMultiple f ∧ 0 ≤ B₀ ∧ B₀.coeff S = 0 ∧
      (∀ A₀ : QDivisor X, A₀.QLinearlyEquivalent A → B.QLinearlyEquivalent (A₀ + B₀)) ∧
      ∀ (N : ℕ) (T : Finset (MMP.Mori.PrimeDivisor X)), ∃ m : ℕ, 0 < m ∧ N ≤ m ∧
        ∃ A₀ : QDivisor X, A₀.QLinearlyEquivalent A ∧ A₀.coeff S = 0 ∧
          (∀ P ∈ T, A₀.coeff P = 0) ∧ ∀ P, A₀.coeff P = 0 ∨ A₀.coeff P = (m : ℚ)⁻¹ := by
  classical
  have : IsIntegral X := hf.isNormalVariety_source.1.toIsIntegral
  obtain ⟨H, hH, hamp, hHamp⟩ := exists_isRelativelyAmple_of_isProjectiveMorphism hproj
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor B
  obtain ⟨c, hc, -⟩ := hQ.2 G
  set r : ℕ := c * N with hr_def
  have hr : 0 < r := Nat.mul_pos hc hN
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  set R : Divisor X := (c : ℤ) • G
  have hRc : ∀ P, (R.coeff P : ℚ) = r * B.coeff P := by
    intro P
    have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hG
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    simp only [R, DivisorWithCoeffs.coeff_smul, smul_eq_mul, Int.cast_mul, this, hr_def]
    push_cast; ring
  set D : Divisor X := R - H
  obtain ⟨E, hE0, ⟨ψ, hψ⟩, hES⟩ := hf.exists_nonneg_linearlyEquivalent_coeff_eq_zero S D
  have hψc : ∀ P, E.coeff P - (R.coeff P - H.coeff P) = P.ord ψ := by
    intro P
    have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hψ
    simpa [D, DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] using this
  refine ⟨(r : ℚ)⁻¹ • Divisor.toQDivisor H, (r : ℚ)⁻¹ • Divisor.toQDivisor E,
    ⟨r, hr, H, hH, ?_, hamp⟩, ?_, ?_, ?_, ?_⟩
  · ext P
    simp [DivisorWithCoeffs.coeff_smul, hrQ]
  · intro P
    have := hE0 P
    change (0 : ℚ) ≤ (r : ℚ)⁻¹ * (E P : ℚ)
    have : (0 : ℚ) ≤ (E P : ℚ) := by exact_mod_cast this
    positivity
  · simp [DivisorWithCoeffs.coeff_smul, hES]
  · rintro A₀ ⟨m, hm, φ, hφ⟩
    have hφc : ∀ P, (m : ℚ) * (A₀.coeff P - (r : ℚ)⁻¹ * H.coeff P) = P.ord φ := by
      intro P
      have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hφ
      simpa [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] using this
    refine ⟨m * r, Nat.mul_pos hm hr, (ψ ^ m * φ ^ r)⁻¹, ?_⟩
    ext P
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
      PrimeDivisor.ord_inv, PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, smul_eq_mul,
      zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    have h1 : (E.coeff P : ℚ) - ((R.coeff P : ℚ) - H.coeff P) = (P.ord ψ : ℚ) := by
      exact_mod_cast hψc P
    rw [← h1, ← hφc P, hRc P]
    field_simp
    ring
  · intro N' T
    obtain ⟨n, hn, hNn, D', ⟨χ, hχ⟩, hD'T, hD'01⟩ :=
      exists_linearlyEquivalent_nsmul_reduced_of_isAmple hf.isNormalVariety_source H hH hHamp N'
        (insert S T)
    have hD'S := hD'T S (Finset.mem_insert_self S T)
    refine ⟨r * n, Nat.mul_pos hr hn, le_trans hNn (Nat.le_mul_of_pos_left n hr),
      ((r * n : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor D', ⟨r * n, Nat.mul_pos hr hn, χ, ?_⟩, ?_, ?_, ?_⟩
    · ext P
      have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hχ
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
        coeff_principalDivisor, smul_eq_mul] at this
      simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
        Divisor.coeff_toQDivisor, coeff_principalDivisor, smul_eq_mul, zsmul_eq_mul, ← this]
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
    · simp [DivisorWithCoeffs.coeff_smul, hD'S]
    · intro P hP
      simp [DivisorWithCoeffs.coeff_smul, hD'T P (Finset.mem_insert_of_mem hP)]
    · intro P
      rcases hD'01 P with h | h
      · exact Or.inl (by simp [DivisorWithCoeffs.coeff_smul, h])
      · exact Or.inr (by simp [DivisorWithCoeffs.coeff_smul, h])

end AmpleDecomposition

end MMP.Fourfold

end
