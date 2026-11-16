module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumTerminal
public import MMP.AlgebraicGeometry.Singularities.LogResolution.RoundUpPushforward
public import MMP.AlgebraicGeometry.Vanishing.KltLogResolutionDirectImage
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Vanishing.PullbackAmpleRoundUp

section

/-!
## Proof outline

Let `(X₀, B₀)` be a klt pair with `X₀` projective over an algebraically closed field `k` of
characteristic zero, `f₀ : X₀ ⟶ S₀` projective, `g : S ⟶ S₀` étale and `X = X₀ ×_{S₀} S` with
projections `q : X ⟶ X₀` and `f : X ⟶ S`. For a line bundle `𝓛` with `𝓛^{⊗ m} ≅ q^*𝒪(D) ⊗ 𝓜`,
`D = m (K_{X₀} + B₀)` Cartier and `𝓜` `f`-ample, `R^i f_* 𝓛 = 0` for `i > 0`.

Let `p₀ : Y₀ ⟶ X₀` be a projective log resolution of `(X₀, B₀)` with crepant boundary `Δ_Y`, and
`E₀ = max (-Δ_Y, 0)`. Then `R^j p₀_* 𝒪_{Y₀}(⌈E₀⌉) = 0` for `j > 0` and
`p₀_* 𝒪_{Y₀}(⌈E₀⌉) = 𝒪_{X₀}`. Base change along the flat `q` gives `p : Y ⟶ X` and
`q' : Y ⟶ Y₀` with the same two properties for `𝒩 = q'^* 𝒪_{Y₀}(⌈E₀⌉)`. By the projection
formula, `𝒢 = 𝒩 ⊗ p^* 𝓛` has `R^j p_* 𝒢 = 0` for `j > 0` and `p_* 𝒢 ≅ 𝓛`, so the Leray
spectral sequence of `p ≫ f` collapses and `R^i f_* 𝓛 ≅ R^i (p ≫ f)_* 𝒢`.

The vanishing of `R^i (p ≫ f)_* 𝒢` is local on `S`. Over an affine open `V ⊆ S`, the normal
scheme `f⁻¹ V` is a finite disjoint union of integral opens `U`. Each `U` is a closed subscheme
of `X₀ ×_k V`, and finitely many sections of `V` define it. So `U` is H-projective over an affine
`k`-variety `T`, the spectrum of the finitely generated algebra they generate. The preimage
`Y' = p⁻¹ U` is integral: `p` is an open immersion over the dense open where `p₀` is one. `Y'`
is smooth and birational over `U`. With `q'' : Y' ⟶ Y₀` the étale restriction of `q'`:
* a canonical divisor `K_{Y₀}` and `D_Y = p₀^* D = m (K_{Y₀} + Δ_Y)` pull back to `Y'` with the
  same coefficients;
* `𝓛|_{Y'} = 𝒪(w_𝓛)`, `𝓜|_U` is ample over `T`, and `p^*(𝓜|_U) = 𝒪(w)` for
  `w = m w_𝓛 - q''^* D_Y`;
* `K_{Y'} + ⌈w / m⌉ = w_𝓛 + q''^* ⌈E₀⌉`, whose fractional part is snc because snc support
  pulls back along étale maps.
Relative round-up vanishing for the pull-back of a relatively ample sheaf, along `Y' ⟶ U ⟶ T`,
kills the higher direct images of `𝒪_{Y'}(K_{Y'} + ⌈w/m⌉) ≅ 𝒢|_{Y'}`. Since `T` is affine, it
then kills `Hⁱ(Y', 𝒢)` for `i > 0`, and Mayer–Vietoris over the disjoint pieces gives the
vanishing on `(p ≫ f)⁻¹ V`.

## Implementation notes

* Relative round-up vanishing is applied in sheaf form,
  `MMP.Fourfold.isZero_rightDerived_pushforward_comp_roundUp_of_pullback_iso`: the input is an
  `f`-ample invertible sheaf `𝓐` together with a divisor `w` on `Y` such that `p^*𝓐 ≅ 𝒪_Y(w)`,
  since `𝓜|_U` is a line bundle that need not come from a Cartier divisor on `U`.
* The étale `g` is arbitrary, so `S` need not be of finite type over `k`. The spreading-out step
  replaces the affine `V` by an affine `k`-variety `T`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64,
  Thm. 2.70, Thm. 5.22
-/

namespace MMP.FourfoldProofs.FourfoldEtaleProjectiveKltAmpleVanishingProof

section EtaleNormal

open TensorProduct

/-- In a reduced Artinian ring every element is `t * t * x` for some `x`. -/
private theorem exists_mul_mul_eq_of_isArtinianRing {T : Type*} [CommRing T] [IsArtinianRing T]
    [IsReduced T] (t : T) : ∃ x, t * t * x = t := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd t (1 : T)
  simp only [smul_eq_mul, mul_one] at hy
  refine ⟨y, ?_⟩
  have h0 : t ^ (n + 1) * (1 - t * y) = 0 := by
    have : t ^ (n + 1) * (1 - t * y) = t ^ (n + 1) - t * (t ^ (n + 1) * y) := by ring
    rw [this, hy, ← pow_succ']; ring
  have h : (t * (1 - t * y)) ^ (n + 1) = 0 := by
    rw [show (t * (1 - t * y)) ^ (n + 1) = t ^ (n + 1) * (1 - t * y) * (1 - t * y) ^ n by
        rw [mul_pow, pow_succ (1 - t * y)]; ring,
      h0, zero_mul]
  have := IsReduced.eq_zero _ ⟨_, h⟩
  linear_combination -this

/-- A nontrivial ring in which every element is `t * t * x` and whose only idempotents are `0`
and `1` is a field. -/
private theorem isField_of_forall_exists_mul_mul_eq {C : Type*} [CommRing C] [Nontrivial C]
    (hC : ∀ t : C, ∃ x, t * t * x = t) (hid : ∀ e : C, e * e = e → e = 0 ∨ e = 1) :
    IsField C := by
  refine ⟨exists_pair_ne C, mul_comm, fun {t} ht => ?_⟩
  obtain ⟨x, hx⟩ := hC t
  refine ⟨x, ?_⟩
  rcases hid (t * x) (by linear_combination x * hx) with h | h
  · exact absurd (by linear_combination -hx + t * h) ht
  · exact h

/-- Being von Neumann regular passes to localizations. -/
private theorem forall_exists_mul_mul_eq_localization {T : Type} [CommRing T] (N : Submonoid T)
    (hT : ∀ t : T, ∃ x, t * t * x = t) (c : Localization N) : ∃ x, c * c * x = c := by
  obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective N c
  obtain ⟨x, hx⟩ := hT t
  refine ⟨IsLocalization.mk' (Localization N) (x * s) (1 : N), ?_⟩
  rw [← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, mul_one]
  rw [show (s : T) * (t * t * (x * ↑s)) = (t * t * x) * (↑s * ↑s) by ring, hx, mul_comm]

/-- If a local ring `A` injects into `C` and is integrally closed in it, the idempotents of `C`
are `0` and `1`. -/
private theorem eq_zero_or_eq_one_of_mul_self_eq {A C : Type} [CommRing A] [IsLocalRing A]
    [CommRing C] [Algebra A C] (hAC : Function.Injective (algebraMap A C))
    (hclC : ∀ c : C, IsIntegral A c → c ∈ (algebraMap A C).range) (e : C) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨a, rfl⟩ := hclC e ⟨Polynomial.X ^ 2 - Polynomial.X,
    (Polynomial.monic_X_pow 2).sub_of_left (by
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]; norm_num), by simp [sq, he]⟩
  have ha : a * a = a := hAC (by rw [map_mul, he])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right; rw [show a = 1 by simpa using h.mul_left_cancel (by rw [mul_one, ha]), map_one]
  · left
    have : (1 - a) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
    rw [show a = 0 by simpa using h.mul_right_eq_zero.mp this, map_zero]

/-- A ring that injects into a field and is integrally closed in it is a normal domain. -/
private theorem isDomain_and_isIntegrallyClosed_of_isField {A C : Type} [CommRing A]
    [CommRing C] [Algebra A C] (hAC : Function.Injective (algebraMap A C))
    (hclC : ∀ c : C, IsIntegral A c → c ∈ (algebraMap A C).range) (hC : IsField C) :
    IsDomain A ∧ IsIntegrallyClosed A := by
  letI := hC.toField
  haveI : IsDomain A := hAC.isDomain _
  refine ⟨‹_›, ?_⟩
  let φ : FractionRing A →+* C := IsFractionRing.lift hAC
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, ha⟩ := hclC (φ x) (hx.map_of_comp_eq (RingHom.id A) φ
    (RingHom.ext fun a => (IsFractionRing.lift_algebraMap hAC a).symm))
  exact ⟨a, φ.injective ((IsFractionRing.lift_algebraMap hAC a).trans ha)⟩

/-- Let `S ⟶ T` be injective with `S` integrally closed in `T`, and `T` von Neumann regular.
Then the local rings of `S` are normal domains. -/
private theorem isDomain_and_isIntegrallyClosed_localization_of_forall {S T : Type} [CommRing S]
    [CommRing T] [Algebra S T] (hinj : Function.Injective (algebraMap S T))
    (hcl : ∀ t : T, IsIntegral S t → t ∈ (algebraMap S T).range)
    (hT : ∀ t : T, ∃ x, t * t * x = t) (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  -- the localization `C` of `T` at `q`
  let M := q.primeCompl
  let A := Localization.AtPrime q
  let C := Localization (Algebra.algebraMapSubmonoid T M)
  have hAC : Function.Injective (algebraMap A C) :=
    haveI : IsLocalization (M.map (algebraMap S T)) C :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid T M) C)
    IsLocalization.map_injective_of_injective _ _ _ hinj
  have hclC : ∀ c : C, IsIntegral A c → c ∈ (algebraMap A C).range := by
    intro c hc
    obtain ⟨⟨m, hm⟩, hmc⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M c hc
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid T M) (m • c)
    obtain ⟨s₀, hs₀, hs⟩ := s.2
    have ht : IsIntegral S (algebraMap T C t) := by
      simp only at hts
      rw [← hts, ← hs]
      exact hmc.mul isIntegral_algebraMap
    obtain ⟨m', hm', hm't⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map M ht
    obtain ⟨u, hu⟩ := hcl _ hm't
    set w : M := ⟨m' * s₀ * m, mul_mem (mul_mem hm' hs₀) hm⟩
    refine ⟨IsLocalization.mk' A u w, ?_⟩
    have hw : IsUnit (algebraMap S C w) := by
      rw [IsScalarTower.algebraMap_apply S T C]
      exact IsLocalization.map_units C (⟨_, w, w.2, rfl⟩ : Algebra.algebraMapSubmonoid T M)
    refine hw.mul_left_injective ?_
    simp only
    rw [IsScalarTower.algebraMap_apply S A C, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply S A C, ← IsScalarTower.algebraMap_apply S A C,
      IsScalarTower.algebraMap_apply S T C, hu, IsScalarTower.algebraMap_apply S T C (w : S)]
    simp only [Submonoid.smul_def, Algebra.smul_def] at hts ⊢
    rw [map_mul, ← hts, ← hs]
    simp only [w, map_mul, ← IsScalarTower.algebraMap_apply S T C]
    ring
  have hC : ∀ c : C, ∃ x, c * c * x = c :=
    forall_exists_mul_mul_eq_localization (Algebra.algebraMapSubmonoid T M) hT
  have hid := eq_zero_or_eq_one_of_mul_self_eq hAC hclC
  haveI : Nontrivial C := hAC.nontrivial
  exact isDomain_and_isIntegrallyClosed_of_isField hAC hclC
    (isField_of_forall_exists_mul_mul_eq hC hid)

/-- The local rings of an étale algebra over a normal domain are normal domains. -/
private theorem isDomain_and_isIntegrallyClosed_localization_of_etale
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  set K := FractionRing R
  set T := S ⊗[R] K
  -- `S ⟶ T` is injective and `S` is integrally closed in `T`
  have hinj : Function.Injective (algebraMap S T) :=
    Algebra.TensorProduct.includeLeft_injective (S := S) (IsFractionRing.injective R K)
  have hcl : ∀ t : T, IsIntegral S t → t ∈ (algebraMap S T).range := by
    intro t ht
    obtain ⟨x, hx⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S)
      (B := K)).2 ⟨t, ht⟩
    have key : ∀ y : S ⊗[R] integralClosure R K,
        ((TensorProduct.toIntegralClosure R S K y : integralClosure S T) : T) ∈
          (algebraMap S T).range := by
      intro y
      induction y with
      | add a b ha hb => simpa using add_mem ha hb
      | tmul s z =>
        obtain ⟨r, hr⟩ : (z : K) ∈ (⊥ : Subalgebra R K) := by
          rw [← IsIntegrallyClosed.integralClosure_eq_bot R K]; exact z.2
        refine ⟨r • s, ?_⟩
        simp only [TensorProduct.toIntegralClosure, ← hr, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_eq_smul_one]
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, ← hr]
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          TensorProduct.smul_tmul']
    have := key x
    rwa [hx] at this
  -- `T` is reduced and von Neumann regular
  have hT : ∀ t : T, ∃ x, t * t * x = t := by
    have : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free _ _
    have : IsArtinianRing (K ⊗[R] S) := IsArtinianRing.of_finite K _
    have : IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K _
    let e := (Algebra.TensorProduct.comm R S K).toRingEquiv
    intro t
    obtain ⟨x, hx⟩ := exists_mul_mul_eq_of_isArtinianRing (e t)
    exact ⟨e.symm x, e.injective (by simpa using hx)⟩
  exact isDomain_and_isIntegrallyClosed_localization_of_forall hinj hcl hT q

end EtaleNormal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Naturally isomorphic additive functors have isomorphic right derived functors. -/
private def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

section Helpers

/-- `R⁰₊ p_* ≅ p_*`. -/
private def rightDerivedPlusZeroIso {X Y : Scheme.{0}} (p : Y ⟶ X)
    [HasDerivedCategory Y.Modules] [HasDerivedCategory X.Modules] :
    (Scheme.Modules.pushforward p).rightDerivedPlus (0 : ℤ) ≅ Scheme.Modules.pushforward p :=
  (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p) 0).symm ≪≫
    (Scheme.Modules.pushforward p).rightDerivedZeroIsoSelf

private theorem isZero_rightDerived_tensorRightInvertible_pullback {X Y : Scheme.{0}}
    (f : Y ⟶ X) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] (M : Y.Modules) (q : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible Y
        ((Scheme.Modules.pullback f).obj N)).obj M)) := by
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N :=
    Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule X N
  have h' : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj M) :=
    h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app M).symm
  have hT : IsZero ((Stacks.ProjectionFormula.tensorRightInvertible X N).obj
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj M)) :=
    (Stacks.ProjectionFormula.tensorRightInvertible X N).map_isZero h'
  exact (hT.of_iso (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso f N M q)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app _)

/-- Projection formula in degree zero with a trivial direct image. -/
private def pushforwardTensorPullbackIso {X Y : Scheme.{0}} (p : Y ⟶ X)
    (N : Y.Modules) (e : (Scheme.Modules.pushforward p).obj N ≅ SheafOfModules.unit X.ringCatSheaf)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛] :
    (Scheme.Modules.pushforward p).obj ((Stacks.ProjectionFormula.tensorRightInvertible Y
        ((Scheme.Modules.pullback p).obj 𝓛)).obj N) ≅ 𝓛 :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 𝓛 :=
    Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule X 𝓛
  ((rightDerivedPlusZeroIso p).app _).symm ≪≫
    Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso p 𝓛 N 0 ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      ((rightDerivedPlusZeroIso p).app N ≪≫ e)).app 𝓛 ≪≫
    Stacks.AffineProjectionFormula.structureUnitor 𝓛

/-- Degree-zero flat base change of a direct image isomorphic to the structure sheaf. -/
private def pushforwardPullbackIsoUnit {X X₀ Y Y₀ : Scheme.{0}} {q' : Y ⟶ Y₀}
    {p : Y ⟶ X} {p₀ : Y₀ ⟶ X₀} {q : X ⟶ X₀} (H : IsPullback q' p p₀ q) [Flat q]
    [QuasiCompact p₀] [QuasiSeparated p₀] (F : Y₀.Modules) [F.IsQuasicoherent]
    (e₀ : (Scheme.Modules.pushforward p₀).obj F ≅ SheafOfModules.unit X₀.ringCatSheaf) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback q').obj F) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard X₀.Modules
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard Y₀.Modules
  ((rightDerivedPlusZeroIso p).app _).symm ≪≫
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso H F 0).symm ≪≫
    (Scheme.Modules.pullback q).mapIso ((rightDerivedPlusZeroIso p₀).app F ≪≫ e₀) ≪≫
    Scheme.Modules.pullbackUnitIso q

/-- **Vanishing of a higher direct image survives flat base change** ([Stacks, Tag 02KH]). -/
private theorem isZero_rightDerived_pushforward_of_isPullback {X X' S S' : Scheme.{0}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X} (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived n).obj
      ((Scheme.Modules.pullback g').obj F)) := by
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard S.Modules
  letI := HasDerivedCategory.standard X'.Modules
  letI := HasDerivedCategory.standard S'.Modules
  rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff] at h ⊢
  exact ((Scheme.Modules.pullback g).map_isZero h).of_iso
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso H F n).symm

end Helpers

section Collapse2

/-- **Leray collapse.** If `R^j p_* M = 0` for `j > 0`, then `R^i (p ≫ f)_* M = 0` implies
`R^i f_*(p_* M) = 0`. -/
private theorem isZero_rightDerived_pushforward_of_comp {X Y S : Scheme.{0}} (p : Y ⟶ X)
    (f : X ⟶ S) (M : Y.Modules)
    (hM : ∀ j : ℕ, 0 < j → IsZero (((Scheme.Modules.pushforward p).rightDerived j).obj M))
    (i : ℕ) (h : IsZero (((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj M)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      ((Scheme.Modules.pushforward p).obj M)) := by
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard S.Modules
  refine (h.of_iso ?_).of_iso (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward p)
    (Scheme.Modules.pushforward f) (fun I hI => by
      haveI := hI
      exact
        Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.rightAcyclic_pushforward_obj_injective
          p f I) hM i).symm
  exact (rightDerivedIsoOfIso (Scheme.Modules.pushforwardComp p f) i).app M

/-- **Vanishing along a resolution with trivial direct image.** Let `p : Y ⟶ X` and `f : X ⟶ S`,
and let `𝒩` on `Y` have `R^j p_* 𝒩 = 0` for `j > 0` and `p_* 𝒩 ≅ 𝒪_X`. For an invertible `𝓛` on
`X`, `R^i (p ≫ f)_*(𝒩 ⊗ p^* 𝓛) = 0` implies `R^i f_* 𝓛 = 0`. -/
private theorem isZero_rightDerived_pushforward_of_comp_tensor_pullback {X Y S : Scheme.{0}}
    (p : Y ⟶ X) (f : X ⟶ S) (N : Y.Modules)
    (hN : ∀ j : ℕ, 0 < j → IsZero (((Scheme.Modules.pushforward p).rightDerived j).obj N))
    (eN : (Scheme.Modules.pushforward p).obj N ≅ SheafOfModules.unit X.ringCatSheaf)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛] (i : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible Y
        ((Scheme.Modules.pullback p).obj 𝓛)).obj N))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj 𝓛) :=
  (isZero_rightDerived_pushforward_of_comp p f _
    (fun j hj => isZero_rightDerived_tensorRightInvertible_pullback p 𝓛 N j (hN j hj)) i h).of_iso
    (((Scheme.Modules.pushforward f).rightDerived i).mapIso
      (pushforwardTensorPullbackIso p N eN 𝓛)).symm

end Collapse2

section Disjoint

/-- **Cohomology over a disjoint union.** If `U ⊓ V = ⊥` and `Hⁿ(U, F) = Hⁿ(V, F) = 0`, then
`Hⁿ(U ⊔ V, F) = 0`: the Mayer–Vietoris sequence has vanishing overlap terms. -/
private theorem isZero_Hgroup_sup_of_inf_eq_bot {X : Scheme.{0}} (U V : X.Opens)
    (hUV : U ⊓ V = ⊥) (F : X.Modules) (n : ℕ) (hU : IsZero (Hgroup X.ringCatSheaf U n F))
    (hV : IsZero (Hgroup X.ringCatSheaf V n F)) :
    IsZero (Hgroup X.ringCatSheaf (U ⊔ V) n F) := by
  have h0 : ∀ m, Subsingleton (Hgroup X.ringCatSheaf (U ⊓ V) m F) := fun m => by
    rw [← AddCommGrpCat.isZero_iff_subsingleton, hUV]; exact isZero_Hgroup_bot F m
  rw [AddCommGrpCat.isZero_iff_subsingleton] at hU hV ⊢
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : Hgroup X.ringCatSheaf (U ⊔ V) n F, z = 0 by rw [h x, h y]
  intro z
  cases n with
  | zero =>
    exact Stacks.Cohomology.AmbientMayerVietoris.eq_zero_of_restrict_eq_zero X.ringCatSheaf U V F
      (U ⊔ V) le_sup_left le_sup_right rfl z (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  | succ n =>
    obtain ⟨θ, hθ⟩ := Stacks.Cohomology.AmbientMayerVietoris.exists_ambientDelta_eq
      X.ringCatSheaf U V F (U ⊔ V) le_sup_left le_sup_right rfl n z (Subsingleton.elim _ _)
      (Subsingleton.elim _ _)
    rw [← hθ, Subsingleton.elim θ 0, map_zero]

/-- **Cohomology over a finite disjoint union.** -/
private theorem isZero_Hgroup_finsetSup {X : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (U : ι → X.Opens) (hd : (s : Set ι).PairwiseDisjoint U) (F : X.Modules) (n : ℕ)
    (h : ∀ c ∈ s, IsZero (Hgroup X.ringCatSheaf (U c) n F)) :
    IsZero (Hgroup X.ringCatSheaf (s.sup U) n F) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isZero_Hgroup_bot F n
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    refine isZero_Hgroup_sup_of_inf_eq_bot _ _ ?_ F n (h a (Finset.mem_insert_self a s))
      (ih (hd.subset (by simp)) fun c hc => h c (Finset.mem_insert_of_mem hc))
    refine disjoint_iff.mp (Finset.disjoint_sup_right.mpr fun c hc => ?_)
    exact hd (by simp) (by simp [hc]) (by rintro rfl; exact ha hc)

section EtaleNormalScheme

/-- **Étale over normal is normal.** -/
private theorem isNormal_of_etale {X Y : Scheme.{0}} (q : X ⟶ Y) [Etale q] [IsIntegral Y]
    [IsNormal Y] : IsNormal X := by
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ q ⁻¹ᵁ V from hxV) (q ⁻¹ᵁ V).isOpen
    haveI : Nonempty V := ⟨⟨q x, hxV⟩⟩
    haveI : IsDomain Γ(Y, V) := IsIntegral.component_integral V
    haveI : IsIntegrallyClosed Γ(Y, V) :=
      (isNormal_iff_forall_affineOpen_normal Y).mp inferInstance ⟨V, hV⟩ inferInstance
    letI : Algebra Γ(Y, V) Γ(X, U) := (q.appLE V U hUV).hom.toAlgebra
    haveI : Algebra.Etale Γ(Y, V) Γ(X, U) := q.etale_appLE hV hU hUV
    set p := hU.primeIdealOf ⟨x, hxU⟩
    obtain ⟨h1, h2⟩ := isDomain_and_isIntegrallyClosed_localization_of_etale (R := Γ(Y, V))
      p.asIdeal
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    let e := IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (X.presheaf.stalk x)
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

end EtaleNormalScheme

/-- A point whose local ring is a domain lies on only one irreducible component. -/
private theorem eq_of_mem_irreducibleComponents_of_isDomain_stalk {Y : Scheme.{0}} (x : Y)
    [IsDomain (Y.presheaf.stalk x)] {Z₁ Z₂ : Set Y} (hZ₁ : Z₁ ∈ irreducibleComponents Y)
    (hZ₂ : Z₂ ∈ irreducibleComponents Y) (h₁ : x ∈ Z₁) (h₂ : x ∈ Z₂) : Z₁ = Z₂ := by
  set η := Y.fromSpecStalk x (genericPoint (Spec (Y.presheaf.stalk x)))
  have key : ∀ Z ∈ irreducibleComponents Y, x ∈ Z → closure ({η} : Set Y) = Z := by
    intro Z hZ hx
    have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents _ hZ
    have hgen := hZ.1.isGenericPoint_genericPoint_closure
    rw [hZc.closure_eq] at hgen
    have hsp : hZ.1.genericPoint ⤳ x := hgen.specializes hx
    obtain ⟨q, hq⟩ : hZ.1.genericPoint ∈ Set.range (Y.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]; exact hsp
    have hηξ : η ⤳ hZ.1.genericPoint := by
      rw [← hq]
      exact (genericPoint_specializes q).map (Y.fromSpecStalk x).continuous
    have hsub : Z ⊆ closure ({η} : Set Y) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hηξ))
        isClosed_closure
    exact le_antisymm (hZ.2 isIrreducible_singleton.closure hsub) hsub
  exact (key Z₁ hZ₁ h₁).symm.trans (key Z₂ hZ₂ h₂)

/-- In a normal scheme with finitely many irreducible components, each component is open. -/
private theorem isOpen_of_mem_irreducibleComponents {W : Scheme.{0}} [IsNormal W]
    (hfin : (irreducibleComponents W).Finite) {Z : Set W} (hZ : Z ∈ irreducibleComponents W) :
    IsOpen Z := by
  have h : Zᶜ = ⋃ Z' ∈ irreducibleComponents W \ {Z}, Z' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨Z', hZ', hsub⟩ :=
        exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
      exact ⟨Z', ⟨hZ', by rintro rfl; exact hx (hsub rfl)⟩, hsub rfl⟩
    · rintro ⟨Z', ⟨hZ', hne⟩, hx⟩ hxZ
      exact hne (eq_of_mem_irreducibleComponents_of_isDomain_stalk x hZ' hZ hx hxZ)
  rw [← isClosed_compl_iff, h]
  exact (hfin.diff).isClosed_biUnion fun Z' hZ' => isClosed_of_mem_irreducibleComponents _ hZ'.1

/-- **Decomposition into integral pieces.** A quasi-compact open of a locally Noetherian normal
scheme is a finite disjoint union of integral opens. -/
private theorem exists_finset_pairwiseDisjoint_isIntegral {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (O : X.Opens) (hO : IsCompact (O : Set X)) :
    ∃ (ι : Type) (t : Finset ι) (U : ι → X.Opens), (t : Set ι).PairwiseDisjoint U ∧
      t.sup U = O ∧ ∀ c, IsIntegral (U c).toScheme := by
  classical
  haveI : CompactSpace O := isCompact_iff_compactSpace.mp hO
  haveI : IsNoetherian O.toScheme := ⟨⟩
  have hfin : (irreducibleComponents O.toScheme).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  haveI : Fintype (irreducibleComponents O.toScheme) := hfin.fintype
  let V : irreducibleComponents O.toScheme → O.toScheme.Opens := fun Z =>
    ⟨Z.1, isOpen_of_mem_irreducibleComponents hfin Z.2⟩
  refine ⟨irreducibleComponents O.toScheme, Finset.univ, fun Z => O.ι ''ᵁ V Z, ?_, ?_, ?_⟩
  · intro a _ b _ hab
    rw [Function.onFun, disjoint_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_image, Set.mem_inter_iff,
      Set.mem_image, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨y, hy, rfl⟩ ⟨y', hy', hyy⟩
    obtain rfl := O.ι.isOpenEmbedding.injective hyy
    exact hab (Subtype.ext (eq_of_mem_irreducibleComponents_of_isDomain_stalk _ a.2 b.2 hy hy'))
  · ext x
    simp only [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_set_eq_biUnion,
      Function.comp_apply, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Scheme.Hom.coe_image, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨Z, y, -, rfl⟩
      exact y.2
    · intro hx
      obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        {(⟨x, hx⟩ : O.toScheme)} isIrreducible_singleton
      exact ⟨⟨Z, hZ⟩, ⟨x, hx⟩, hsub rfl, rfl⟩
  · intro Z
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    haveI : Nonempty (V Z) := ⟨⟨z, hz⟩⟩
    haveI : IsIntegral (V Z).toScheme := by
      haveI : IrreducibleSpace (V Z) := isIrreducible_iff_irreducibleSpace.mp Z.2.1
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    haveI : Nonempty (O.ι ''ᵁ V Z) := ⟨(O.ι.isoImage (V Z)).hom ⟨z, hz⟩⟩
    exact isIntegral_of_isOpenImmersion (O.ι.isoImage (V Z)).inv

end Disjoint

section SpreadingOut

open TensorProduct

/-- In a pushout square of commutative rings, the pushout is generated as a ring by the images
of the two legs. -/
private theorem mem_closure_range_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (x : P) :
    x ∈ Subring.closure (Set.range inl ∪ Set.range inr) := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  have h' := CommRingCat.isPushout_tensorProduct A B C
  let e := h'.isoIsPushout _ _ h
  obtain ⟨t, rfl⟩ : ∃ t, e.hom t = x := ⟨e.inv x, by simp⟩
  have hl : ∀ b, e.hom (b ⊗ₜ 1) = inl b := fun b =>
    congr($(h'.inl_isoIsPushout_hom _ _ h).hom b)
  have hr : ∀ c, e.hom (1 ⊗ₜ c) = inr c := fun c =>
    congr($(h'.inr_isoIsPushout_hom _ _ h).hom c)
  change B ⊗[A] C at t
  induction t using TensorProduct.induction_on with
  | zero => simpa using Subring.zero_mem _
  | add a b ha hb => simpa using Subring.add_mem _ ha hb
  | tmul b c =>
    have : b ⊗ₜ[A] c = (b ⊗ₜ (1 : C)) * ((1 : B) ⊗ₜ c) := by simp
    rw [this, map_mul, hl, hr]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨b, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨c, rfl⟩))

/-- If `A` is a finitely generated `K`-algebra generated as a ring by a subset `S` containing the
scalars and the range of a ring map `β : M →+* A`, then finitely many elements of `M` suffice. -/
private theorem exists_finset_closure_eq_top {K M A : Type*} [CommRing K] [CommRing M] [CommRing A]
    [Algebra K A] (hA : Algebra.FiniteType K A) (S : Set A)
    (hK : Set.range (algebraMap K A) ⊆ S) (β : M →+* A)
    (hS : Subring.closure (S ∪ Set.range β) = ⊤) :
    ∃ F : Finset M, Subring.closure (S ∪ β '' F) = ⊤ := by
  classical
  obtain ⟨G, hG⟩ := hA.out
  let Sub : Finset M → Subring A := fun F => Subring.closure (S ∪ β '' F)
  have hmono : Monotone Sub := fun F F' h =>
    Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))
  have hdir : Directed (· ≤ ·) Sub := hmono.directed_le
  have hle : Subring.closure (S ∪ Set.range β) ≤ ⨆ F, Sub F := by
    rw [Subring.closure_le]
    rintro x (hx | ⟨m, rfl⟩)
    · exact (Subring.mem_iSup_of_directed hdir).2 ⟨∅, Subring.subset_closure (Or.inl hx)⟩
    · exact (Subring.mem_iSup_of_directed hdir).2
        ⟨{m}, Subring.subset_closure (Or.inr ⟨m, by simp, rfl⟩)⟩
  have hy : ∀ y : A, ∃ F, y ∈ Sub F := fun y =>
    (Subring.mem_iSup_of_directed hdir).1 (hle (hS ▸ Subring.mem_top y))
  choose Fy hFy using hy
  refine ⟨G.biUnion Fy, eq_top_iff.2 fun x _ => ?_⟩
  have hsub : (Algebra.adjoin K (G : Set A)).toSubring ≤ Sub (G.biUnion Fy) := by
    intro z hz
    refine Algebra.adjoin_induction (p := fun z _ => z ∈ Sub (G.biUnion Fy)) ?_ ?_ ?_ ?_ hz
    · intro y hy
      exact hmono (Finset.subset_biUnion_of_mem Fy hy) (hFy y)
    · intro r
      exact Subring.subset_closure (Or.inl (hK ⟨r, rfl⟩))
    · intro u v _ _ hu hv; exact add_mem hu hv
    · intro u v _ _ hu hv; exact mul_mem hu hv
  exact hsub (by rw [hG]; trivial)

section Charts

variable {P T Z : Scheme.{0}} (sP : P ⟶ Z) (sT : T ⟶ Z)

/-- Over an affine open `W` of `P`, the sections of `P ×_Z T` over the preimage of `W` are
generated by the two projections, for `T` and `Z` affine. -/
private theorem closure_range_appTop_restrict_eq_top [IsAffine T] [IsAffine Z] (W : P.Opens)
    (hW : IsAffineOpen W) :
    Subring.closure (Set.range ((pullback.fst sP sT) ∣_ W).appTop ∪
      Set.range ((pullback.fst sP sT ⁻¹ᵁ W).ι ≫ pullback.snd sP sT).appTop) = ⊤ := by
  haveI : IsAffine W.toScheme := hW
  have h := (isPullback_morphismRestrict (pullback.fst sP sT) W).paste_vert
    (IsPullback.of_hasPullback sP sT)
  exact eq_top_iff.2 fun x _ => mem_closure_range_of_isPushout (isPushout_appTop_of_isPullback h) x

/-- A closed immersion into `P ×_Z V` has affine pieces over the affine opens `W` of `P`, whose
sections are generated by the two projections. -/
private theorem isAffineOpen_and_closure_eq_top_of_isClosedImmersion {U : Scheme.{0}} [IsAffine T]
    [IsAffine Z] (c : U ⟶ pullback sP sT) [IsClosedImmersion c] (W : P.Opens)
    (hW : IsAffineOpen W) :
    IsAffineOpen ((c ≫ pullback.fst sP sT) ⁻¹ᵁ W) ∧
      Subring.closure (Set.range ((c ≫ pullback.fst sP sT) ∣_ W).appTop ∪
        Set.range (((c ≫ pullback.fst sP sT) ⁻¹ᵁ W).ι ≫ c ≫ pullback.snd sP sT).appTop) = ⊤ := by
  set F := pullback.fst sP sT
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffineHom F :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback sP sT).flip
      (inferInstance : IsAffineHom sT)
  have hO : IsAffineOpen (F ⁻¹ᵁ W) := hW.preimage F
  haveI : IsAffine (F ⁻¹ᵁ W).toScheme := hO
  obtain ⟨hA, hs⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (c ∣_ (F ⁻¹ᵁ W))
  refine ⟨hA, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  have hx : x ∈ Subring.closure (Set.range (F ∣_ W).appTop ∪
      Set.range ((F ⁻¹ᵁ W).ι ≫ pullback.snd sP sT).appTop) := by
    rw [closure_range_appTop_restrict_eq_top sP sT W hW]; trivial
  have hmap : (c ∣_ (F ⁻¹ᵁ W)).appTop x ∈
      (Subring.closure (Set.range (F ∣_ W).appTop ∪
        Set.range ((F ⁻¹ᵁ W).ι ≫ pullback.snd sP sT).appTop)).map
          (c ∣_ (F ⁻¹ᵁ W)).appTop.hom := Subring.mem_map.2 ⟨x, hx, rfl⟩
  rw [RingHom.map_closure] at hmap
  refine Subring.closure_mono ?_ hmap
  rintro _ ⟨z, (⟨w, rfl⟩ | ⟨t, rfl⟩), rfl⟩
  · left
    refine ⟨w, ?_⟩
    rw [morphismRestrict_comp, Scheme.Hom.comp_appTop]
    rfl
  · right
    refine ⟨t, ?_⟩
    change ((c ⁻¹ᵁ (F ⁻¹ᵁ W)).ι ≫ c ≫ pullback.snd sP sT).appTop t = _
    rw [← morphismRestrict_ι_assoc, Scheme.Hom.comp_appTop]
    rfl

/-- Conversely, a morphism into `P ×_Z T` whose pieces over an affine open `W` of `P` are affine
with sections generated by the two projections is a closed immersion over `W`. -/
private theorem isClosedImmersion_morphismRestrict_of_closure_eq_top {U : Scheme.{0}} [IsAffine T]
    [IsAffine Z] (c : U ⟶ pullback sP sT) (W : P.Opens) (hW : IsAffineOpen W)
    (hA : IsAffineOpen ((c ≫ pullback.fst sP sT) ⁻¹ᵁ W))
    (hgen : Subring.closure (Set.range ((c ≫ pullback.fst sP sT) ∣_ W).appTop ∪
        Set.range (((c ≫ pullback.fst sP sT) ⁻¹ᵁ W).ι ≫ c ≫ pullback.snd sP sT).appTop) = ⊤) :
    IsClosedImmersion (c ∣_ (pullback.fst sP sT ⁻¹ᵁ W)) := by
  set F := pullback.fst sP sT
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffineHom F :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback sP sT).flip
      (inferInstance : IsAffineHom sT)
  haveI : IsAffine (F ⁻¹ᵁ W).toScheme := hW.preimage F
  haveI : IsAffine (c ⁻¹ᵁ (F ⁻¹ᵁ W)).toScheme := hA
  refine IsClosedImmersion.of_surjective_of_isAffine _ fun y => ?_
  have hy : y ∈ Subring.closure (Set.range ((c ≫ F) ∣_ W).appTop ∪
      Set.range (((c ≫ F) ⁻¹ᵁ W).ι ≫ c ≫ pullback.snd sP sT).appTop) := by
    rw [hgen]; trivial
  have hsub : Set.range ((c ≫ F) ∣_ W).appTop ∪
      Set.range (((c ≫ F) ⁻¹ᵁ W).ι ≫ c ≫ pullback.snd sP sT).appTop ⊆
        ((c ∣_ (F ⁻¹ᵁ W)).appTop.hom.range : Set Γ(c ⁻¹ᵁ (F ⁻¹ᵁ W), ⊤)) := by
    rintro _ (⟨w, rfl⟩ | ⟨t, rfl⟩)
    · refine ⟨(F ∣_ W).appTop w, ?_⟩
      rw [morphismRestrict_comp, Scheme.Hom.comp_appTop]
      rfl
    · refine ⟨((F ⁻¹ᵁ W).ι ≫ pullback.snd sP sT).appTop t, ?_⟩
      change _ = ((c ⁻¹ᵁ (F ⁻¹ᵁ W)).ι ≫ c ≫ pullback.snd sP sT).appTop t
      rw [← morphismRestrict_ι_assoc, Scheme.Hom.comp_appTop]
      rfl
  exact (Subring.closure_le (t := (c ∣_ (F ⁻¹ᵁ W)).appTop.hom.range)).2 hsub hy

end Charts

/-- **Spreading out a closed subscheme of `P ×_k V` that is of finite type over `k`.** Let `V`
be affine and `P` quasi-compact over `Spec k`, and let `U` be an integral closed subscheme of
`P ×_k V` locally of finite type over `k`. Then `U` is a closed subscheme of `P ×_k T`, over
`P`, for an integral affine `T` of finite type over `k`: the spectrum of the subalgebra of
`Γ(U, 𝒪_U)` generated by finitely many sections coming from `V`. -/
private theorem exists_isClosedImmersion_pullback_of_locallyOfFiniteType {k : CommRingCat.{0}}
    {P V U : Scheme.{0}} (sP : P ⟶ Spec k) (sV : V ⟶ Spec k) [CompactSpace P] [IsAffine V]
    [IsIntegral U] (c₀ : U ⟶ pullback sP sV) [IsClosedImmersion c₀]
    [LocallyOfFiniteType (c₀ ≫ pullback.fst sP sV ≫ sP)] :
    ∃ (T : Scheme.{0}) (sT : T ⟶ Spec k) (c : U ⟶ pullback sP sT), IsAffine T ∧
      IsIntegral T ∧ LocallyOfFiniteType sT ∧ IsClosedImmersion c ∧
        c ≫ pullback.fst sP sT = c₀ ≫ pullback.fst sP sV := by
  classical
  set a := c₀ ≫ pullback.fst sP sV with ha
  set b := c₀ ≫ pullback.snd sP sV with hb
  have hasP : LocallyOfFiniteType (a ≫ sP) := by rw [ha, Category.assoc]; infer_instance
  -- over each affine open `W` of `P`, finitely many sections of `V` suffice
  have key : ∀ W : P.affineOpens, ∃ F : Finset Γ(V, ⊤), IsAffineOpen (a ⁻¹ᵁ (W : P.Opens)) ∧
      Subring.closure (Set.range (a ∣_ (W : P.Opens)).appTop ∪
        ((a ⁻¹ᵁ (W : P.Opens)).ι ≫ b).appTop '' F) = ⊤ := by
    intro W
    obtain ⟨hA, hgen⟩ := isAffineOpen_and_closure_eq_top_of_isClosedImmersion sP sV c₀ W W.2
    haveI : IsAffine (a ⁻¹ᵁ (W : P.Opens)).toScheme := hA
    letI : Algebra Γ(Spec k, ⊤) Γ(a ⁻¹ᵁ (W : P.Opens), ⊤) :=
      ((a ⁻¹ᵁ (W : P.Opens)).ι ≫ a ≫ sP).appTop.hom.toAlgebra
    have hft : Algebra.FiniteType Γ(Spec k, ⊤) Γ(a ⁻¹ᵁ (W : P.Opens), ⊤) :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
        (f := (a ⁻¹ᵁ (W : P.Opens)).ι ≫ a ≫ sP)).1 inferInstance
    have hK : Set.range (algebraMap Γ(Spec k, ⊤) Γ(a ⁻¹ᵁ (W : P.Opens), ⊤)) ⊆
        Set.range (a ∣_ (W : P.Opens)).appTop := by
      rintro _ ⟨r, rfl⟩
      refine ⟨((W : P.Opens).ι ≫ sP).appTop r, ?_⟩
      change _ = ((a ⁻¹ᵁ (W : P.Opens)).ι ≫ a ≫ sP).appTop r
      rw [← morphismRestrict_ι_assoc, Scheme.Hom.comp_appTop]
      rfl
    obtain ⟨F, hF⟩ := exists_finset_closure_eq_top hft _ hK
      ((a ⁻¹ᵁ (W : P.Opens)).ι ≫ b).appTop.hom hgen
    exact ⟨F, hA, hF⟩
  choose F hA hF using key
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : P.Opens))).1
    (by simpa using isCompact_univ)
  let G : Finset Γ(V, ⊤) := hs.toFinset.biUnion F
  letI : Algebra k Γ(U, ⊤) := ((Scheme.ΓSpecIso k).inv ≫ (a ≫ sP).appTop).hom.toAlgebra
  let R₀ : Subalgebra k Γ(U, ⊤) := Algebra.adjoin k (b.appTop.hom '' (G : Set Γ(V, ⊤)))
  let φ : CommRingCat.of R₀ ⟶ Γ(U, ⊤) := CommRingCat.ofHom R₀.val.toRingHom
  let ψ : k ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (algebraMap k R₀)
  let sT : Spec (CommRingCat.of R₀) ⟶ Spec k := Spec.map ψ
  obtain ⟨b', hb'⟩ : ∃ b' : U ⟶ Spec (CommRingCat.of R₀),
      b'.appTop = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom ≫ φ :=
    ⟨U.toSpecΓ ≫ Spec.map φ, by
      simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]⟩
  have hcomm : a ≫ sP = b' ≫ sT := by
    refine ext_of_isAffine ?_
    rw [show (b' ≫ sT).appTop = sT.appTop ≫ b'.appTop from Scheme.Hom.comp_appTop _ _, hb',
      ← Category.assoc, Scheme.ΓSpecIso_naturality]
    ext x
    simp only [ψ, φ, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    change _ = algebraMap k Γ(U, ⊤) _
    simp [RingHom.algebraMap_toAlgebra]
  let c : U ⟶ pullback sP sT := pullback.lift a b' hcomm
  have hcfst : c ≫ pullback.fst sP sT = a := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd sP sT = b' := pullback.lift_snd _ _ _
  have hcl : IsClosedImmersion c := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
      (fun W : s => pullback.fst sP sT ⁻¹ᵁ ((W : P.affineOpens) : P.Opens)) ?_ fun W => ?_
    · have : (⨆ W : s, ((W : P.affineOpens) : P.Opens)) = ⊤ := by
        rw [hsU, iSup_subtype']
      rw [← Scheme.Hom.preimage_iSup, this, Scheme.Hom.preimage_top]
    · have hW := (W : P.affineOpens).2
      refine isClosedImmersion_morphismRestrict_of_closure_eq_top sP sT c _ hW
        (by rw [hcfst]; exact hA W) ?_
      rw [hcfst, hcsnd]
      refine eq_top_iff.2 fun x _ => ?_
      have hx : x ∈ Subring.closure (Set.range (a ∣_ ((W : P.affineOpens) : P.Opens)).appTop ∪
          ((a ⁻¹ᵁ ((W : P.affineOpens) : P.Opens)).ι ≫ b).appTop '' F W) := by
        rw [hF W]; trivial
      refine Subring.closure_mono ?_ hx
      rintro _ (h | ⟨m, hm, rfl⟩)
      · exact Or.inl h
      · right
        have hmem : b.appTop m ∈ R₀ := Algebra.subset_adjoin
          ⟨m, Finset.mem_biUnion.2 ⟨W, hs.mem_toFinset.2 W.2, hm⟩, rfl⟩
        have hval : b'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ⟨_, hmem⟩) =
            b.appTop m := by
          rw [hb']; simp [φ]
        refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ⟨_, hmem⟩, ?_⟩
        rw [Scheme.Hom.comp_appTop, CategoryTheory.comp_apply, hval]
        simp only [b, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have hR₀ : Algebra.FiniteType k R₀ :=
    Algebra.FiniteType.adjoin_of_finite ((G : Set Γ(V, ⊤)).toFinite.image _)
  haveI : Nontrivial Γ(U, ⊤) := inferInstance
  refine ⟨Spec (CommRingCat.of R₀), sT, c, inferInstance, inferInstance, ?_, hcl, hcfst⟩
  refine (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 ?_
  exact RingHom.finiteType_algebraMap.2 hR₀

end SpreadingOut

/-- **Cohomology of an open with an affine model.** Let `W` be an open of `Y` and
`h : W ⟶ T` a quasi-compact quasi-separated morphism to an affine scheme. If the restriction of a
module `F` to `W` is isomorphic to a quasi-coherent module with vanishing higher direct images
along `h`, then `Hⁱ(W, F) = 0` for every `i > 0`. -/
private theorem isZero_Hgroup_of_isZero_rightDerived_of_isAffine {Y T : Scheme.{0}}
    (W : Y.Opens) (h : W.toScheme ⟶ T) [IsAffine T] [QuasiCompact h] [QuasiSeparated h]
    (F : Y.Modules) (G : W.toScheme.Modules) [G.IsQuasicoherent]
    (e : (Scheme.Modules.restrictFunctor W.ι).obj F ≅ G)
    (hvan : ∀ j : ℕ, 0 < j → IsZero (((Scheme.Modules.pushforward h).rightDerived j).obj G))
    (i : ℕ) (hi : 0 < i) : IsZero (Hgroup Y.ringCatSheaf W i F) := by
  refine IsZero.of_iso ?_ (Stacks.LocalCohomology.hgroupRestrictIso Y W i F)
  refine IsZero.of_iso ?_ ((Hfunctor W.toScheme.ringCatSheaf ⊤ i).mapIso e)
  haveI := ProperCoherentFiniteType.isQuasicoherent_pushforward h G inferInstance
  exact (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine T _ i hi).of_iso
    (Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages h hvan i)

/-- An open `U` contained in an open `W` and closed in it is a closed subscheme of `W`. -/
private theorem exists_isClosedImmersion_lift {X : Scheme.{0}} {U W : X.Opens} (hUW : U ≤ W)
    (hUcl : ∀ x ∈ W, x ∈ closure (U : Set X) → x ∈ U) :
    ∃ ι' : U.toScheme ⟶ W.toScheme, IsClosedImmersion ι' ∧ ι' ≫ W.ι = U.ι := by
  let ι' : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι U.ι (by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact fun x hx => hUW hx)
  have hι' : ι' ≫ W.ι = U.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨ι', ?_, hι'⟩
  refine IsClosedImmersion.of_isPreimmersion ι' ?_
  have hr : Set.range ι' = W.ι ⁻¹' (U : Set X) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      change (ι' ≫ W.ι) u ∈ U
      rw [hι']
      exact u.2
    · intro hy
      obtain ⟨u, hu⟩ : W.ι y ∈ Set.range U.ι := by
        rwa [Scheme.Opens.range_ι]
      refine ⟨u, W.ι.isOpenEmbedding.injective ?_⟩
      change (ι' ≫ W.ι) u = _
      rw [hι', hu]
  rw [hr, ← closure_subset_iff_isClosed]
  intro y hy
  have hy' := W.ι.isOpenEmbedding.continuous.closure_preimage_subset _ hy
  refine hUcl _ ?_ hy'
  show _ ∈ ((W : X.Opens) : Set X)
  rw [← Scheme.Opens.range_ι]
  exact ⟨y, rfl⟩

/-- **Spreading out an integral piece over an affine variety.** An integral open `U` of the étale
base change `X`, closed in `f⁻¹ V` for an affine open `V ⊆ S`, is H-projective over an affine
`k`-variety `T`, compatibly with the structure morphisms to `Spec k`. -/
private theorem exists_isProjectiveMorphism_isAffine_of_le_preimage
    {k : Type} [Field k] {X₀ : Scheme.{0}} [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {S₀ : Scheme.{0}} (sS₀ : S₀ ⟶ Spec (.of k)) (f₀ : X₀ ⟶ S₀) (hfs : f₀ ≫ sS₀ = sX₀)
    [IsProper f₀]
    {X S : Scheme.{0}} (g : S ⟶ S₀) [Etale g] (q : X ⟶ X₀) (f : X ⟶ S)
    (hpb : IsPullback q f f₀ g) (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) (hUcl : ∀ x ∈ f ⁻¹ᵁ V, x ∈ closure (U : Set X) → x ∈ U)
    (hU : IsIntegral U.toScheme) :
    ∃ (T : Scheme.{0}) (sT : T ⟶ Spec (.of k)) (π : U.toScheme ⟶ T), IsAffine T ∧
      AlgebraicGeometry.IsVariety k sT ∧ IsProjectiveMorphism π ∧
      π ≫ sT = U.ι ≫ q ≫ sX₀ := by
  haveI : IsAffine V.toScheme := hV
  haveI : Etale q := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : IsProper f := MorphismProperty.of_isPullback hpb inferInstance
  -- `f⁻¹ V` is the fibre product `X₀ ×_{S₀} V`
  have hP : IsPullback ((f ⁻¹ᵁ V).ι ≫ q) (f ∣_ V) f₀ (V.ι ≫ g) :=
    (isPullback_morphismRestrict f V).flip.paste_horiz hpb
  let e := hP.isoPullback
  -- the open immersion `U ⟶ f⁻¹ V` has closed image
  obtain ⟨ι', hι'c, hι'⟩ := exists_isClosedImmersion_lift hUV hUcl
  haveI := hι'c
  let c₀ : U.toScheme ⟶ pullback (f₀ ≫ sS₀) ((V.ι ≫ g) ≫ sS₀) :=
    ι' ≫ e.hom ≫ pullback.mapDesc f₀ (V.ι ≫ g) sS₀
  have hc₀ : c₀ ≫ pullback.fst _ _ = U.ι ≫ q := by
    simp only [c₀, Category.assoc, pullback.mapDesc, pullback.lift_fst]
    rw [IsPullback.isoPullback_hom_fst_assoc, Category.comp_id, ← Category.assoc, hι']
  have hsep : IsSeparated (f₀ ≫ sS₀) := by rw [hfs]; infer_instance
  haveI : IsClosedImmersion c₀ := by
    have hsnd : c₀ ≫ pullback.snd _ _ = ι' ≫ (f ∣_ V) := by
      simp only [c₀, Category.assoc, pullback.mapDesc, pullback.lift_snd, Category.comp_id]
      dsimp only [e]
      rw [IsPullback.isoPullback_hom_snd]
    haveI : IsProper (c₀ ≫ pullback.snd _ _) := by rw [hsnd]; infer_instance
    haveI : IsSeparated (pullback.snd (f₀ ≫ sS₀) ((V.ι ≫ g) ≫ sS₀)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hsep
    haveI : UniversallyClosed c₀ := UniversallyClosed.of_comp_of_isSeparated c₀ (pullback.snd _ _)
    exact IsClosedImmersion.of_isPreimmersion c₀ c₀.isClosedMap.isClosed_range
  haveI : LocallyOfFiniteType (c₀ ≫ pullback.fst _ _ ≫ f₀ ≫ sS₀) := by
    rw [← Category.assoc, hc₀, hfs]; infer_instance
  obtain ⟨T, sT, c, hTa, hTi, hTf, hc, hcf⟩ :=
    exists_isClosedImmersion_pullback_of_locallyOfFiniteType (f₀ ≫ sS₀) ((V.ι ≫ g) ≫ sS₀) c₀
  haveI := hTa
  haveI := hTi
  haveI := hTf
  haveI := hc
  have hproj : IsProjectiveMorphism (pullback.snd (f₀ ≫ sS₀) sT) := by
    have h : IsProjectiveMorphism (f₀ ≫ sS₀) := by
      rw [hfs]; exact AlgebraicGeometry.IsProjectiveVariety.isProjective
    exact h.baseChange sT
  obtain ⟨N, i, hi, hif⟩ := hproj
  haveI := hi
  refine ⟨T, sT, c ≫ pullback.snd _ _, hTa, IsVariety.mk,
    ⟨N, c ≫ i, inferInstance, by rw [Category.assoc, hif]⟩, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hcf, hc₀, Category.assoc, hfs]

/-- A point of `O` in the closure of a member `U c` of a finite disjoint family with union `O`
lies in `U c`. -/
private theorem mem_of_mem_closure_of_pairwiseDisjoint {X : Scheme.{0}} {ι : Type} (t : Finset ι)
    (U : ι → X.Opens) (hd : (t : Set ι).PairwiseDisjoint U) {O : X.Opens} (hsup : t.sup U = O)
    {c : ι} (hc : c ∈ t) : ∀ x ∈ O, x ∈ closure (U c : Set X) → x ∈ U c := by
  classical
  intro x hxO hx
  rw [← hsup] at hxO
  obtain ⟨d, hd', hxd⟩ : ∃ d ∈ t, x ∈ U d := by
    have h : x ∈ ((t.sup U : X.Opens) : Set X) := hxO
    simpa [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_set_eq_biUnion] using h
  by_cases hdc : d = c
  · exact hdc ▸ hxd
  · exfalso
    have hdis : Disjoint (U d : Set X) (U c : Set X) := by
      have := hd hd' hc hdc
      rwa [Function.onFun, ← TopologicalSpace.Opens.coe_disjoint] at this
    obtain ⟨y, hy, hyc⟩ := mem_closure_iff.mp hx _ (U d).isOpen hxd
    exact Set.disjoint_left.mp hdis hy hyc

section Auxiliary

/-- The tensor powers of an invertible sheaf `M ≅ 𝒪_X(E)`, `E` Cartier, in the spelling of
`Stacks.Ample.tensorPowModule`: `M^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPowModule_iso_divisorialSheaf {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier)
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (e : M ≅ E.divisorialSheaf) (k : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X M (k : ℤ) ≅ (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫ Divisor.divisorialSheafZeroIso.symm ≪≫
      eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e'⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (k : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e'
        (Stacks.Ample.tensorPowModuleOneIso X _ ≪≫ e) ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData}
    (hF : MMP.Resolution.IsSNCFamily s F)
    {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A prime divisor contained in a closed set of pure codimension one is one of its irreducible
components. -/
private theorem mem_componentsOf_of_support_subset {X : Scheme.{0}} {S : Set X} (hS : IsClosed S)
    (hpure : MMP.Mori.IsPureCodimOne (⟨S, hS⟩ : TopologicalSpace.Closeds X))
    (P : MMP.Mori.PrimeDivisor X) (hP : (P.support : Set X) ⊆ S) :
    (P.support : Set X) ∈ MMP.Resolution.componentsOf S := by
  have hηS : P.genericPoint ∈ S :=
    hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  obtain ⟨W, hW, hηW⟩ := MMP.Resolution.exists_mem_componentsOf hηS
  have hWcl : IsClosed W := MMP.Resolution.isClosed_of_mem_componentsOf hS hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWcl
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X => (W' : Set X) ⊆ S)
      ⟨W, hW.1.1, hWcl⟩ :=
    ⟨hW.1.2, fun W' hW' hle => hW.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hcod := hpure _ hmax
  have hξc : Order.coheight ξ = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    convert hcod using 2
    ext1
    exact hξ.def
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξc with hQ
  have hQs : (Q.support : Set X) = W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hξ.def
  have hPQ : (P.support : Set X) ⊆ Q.support := by
    rw [hQs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  have hPQe := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ
  rw [hPQe, hQs]
  exact hW

/-- A divisor all of whose components lie in an snc closed subset is snc. -/
private theorem isSNC_of_isSNCClosedSubset {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] {S : Set X} (hS : MMP.Resolution.IsSNCClosedSubset sX S)
    {R : Type*} [Zero R] (Δ : MMP.Mori.DivisorWithCoeffs R X)
    (hΔ : ∀ P ∈ Δ.support, (P.support : Set X) ⊆ S) : Δ.IsSNC sX := by
  obtain ⟨hScl, hS0 | ⟨hpure, -, hfam⟩⟩ := hS
  · have hempty : ∀ P ∈ Δ.support, False := fun P hP => by
      have := hΔ P hP (show P.genericPoint ∈ P.support by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
      rw [hS0] at this
      exact this
    refine ⟨fun P hP => (hempty P hP).elim, fun x => ?_⟩
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
    exact ⟨n, z, fun P => (hempty P.1 P.2.1).elim, hz, fun P => (hempty P.1 P.2.1).elim,
      fun P => (hempty P.1 P.2.1).elim⟩
  · exact isSNC_of_isSNCFamily hfam Δ fun P hP =>
      ⟨⟨_, mem_componentsOf_of_support_subset hScl hpure P (hΔ P hP)⟩,
        MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf _ P rfl⟩

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

end Auxiliary

section ResolutionSide

/-- `⌈max c 0⌉ = K + ⌈c - K⌉` for an integer `K` and `c > -1`. -/
private theorem ceil_max_zero_eq_add_ceil (K : ℤ) (c : ℚ) (hc : -1 < c) :
    ⌈max c 0⌉ = K + ⌈-(K : ℚ) + c⌉ := by
  rw [show -(K : ℚ) + c = c + ((-K : ℤ) : ℚ) by push_cast; ring, Int.ceil_add_intCast]
  rcases le_or_gt 0 c with h | h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right h.le, Int.ceil_zero, show ⌈c⌉ = 0 from Int.ceil_eq_iff.2 ⟨by
      push_cast; linarith, by push_cast; linarith⟩]
    ring

/-- **The log resolution side.** On a projective log resolution `p₀ : Y₀ ⟶ X₀` of a klt pair
`(X₀, B₀)` with crepant boundary `Δ_Y`, and for a Cartier divisor `D = m (K₀ + B₀)`, there are a
canonical divisor `K_Y` of `Y₀` and the pull-back `D_Y = p₀^* D` such that
`⌈E₀⌉ = K_Y + ⌈-D_Y / m⌉` for `E₀ = max (-Δ_Y, 0)`, and the fractional part of `-D_Y / m` has
snc support. -/
private theorem exists_canonical_pullback_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X₀ : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {n : ℕ} {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : IsKltPair sX₀ n K₀ B₀)
    (m : ℕ) (hm : 0 < m) (D : Divisor X₀) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K₀ + B₀))
    {Y₀ : Scheme.{0}} (p₀ : Y₀ ⟶ X₀) (hres : IsLogResolution sX₀ (QDivisor.toRDivisor B₀) p₀)
    (hY₀ : IsNormalVariety k (p₀ ≫ sX₀))
    {ΔY : QDivisor Y₀}
    (hΔY : IsCrepantBoundary sX₀ n K₀ B₀ p₀ hY₀ hres.isBirationalMorphism ΔY) :
    haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
    haveI : IsNormal Y₀ := hY₀.2
    ∃ (KY : Divisor Y₀) (DY : Divisor Y₀), KY.IsCanonicalDivisor (p₀ ≫ sX₀) n ∧
      (∃ hB, D.IsPullback p₀ hB DY) ∧
      ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp =
        KY + ((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY)).roundUp ∧
      ((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY)).fract.IsSNC (p₀ ≫ sX₀) := by
  haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
  haveI : IsNormal Y₀ := hY₀.2
  have hbir := hres.isBirationalMorphism
  have hP : IsPairWith sX₀ n K₀ B₀ := hklt.1
  have hXp := (AlgebraicGeometry.isProjectiveVariety_iff k sX₀).1 ‹_›
  haveI : AlgebraicGeometry.IsVariety k sX₀ := hXp.1
  haveI : AlgebraicGeometry.IsVariety k (p₀ ≫ sX₀) := hY₀.1
  haveI : IsIntegral Y₀ := hY₀.1.toIsIntegral
  haveI : IsDominant p₀ := hbir.isDominant
  haveI : IsProper p₀ := hres.isProper
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace (p₀ ≫ sX₀)
  haveI : LocallyOfFiniteType sX₀ := hXp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p₀ ≫ sX₀) := hY₀.1.toLocallyOfFiniteType
  have hsm : IsSmoothScheme (p₀ ≫ sX₀) := hres.isSmoothScheme
  -- `K₀ = div ω` and `K_Y = div p₀^*ω`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hP.1 hP.2.1
  obtain rfl : divisorOfForm ω = K₀ := DivisorWithCoeffs.ext' hωK
  set KY := divisorOfForm (pullbackRationalPluriForms sX₀ p₀ ω) with hKY
  have hQ : (Divisor.toQDivisor (divisorOfForm ω) + B₀).IsQCartier := hP.2.2
  have hsupp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier p₀ hQ
  set P := QDivisor.pullback (f := p₀) (Divisor.toQDivisor (divisorOfForm ω) + B₀) hQ hsupp
    with hPdef
  set C : QDivisor Y₀ := Divisor.toQDivisor KY - P with hCdef
  have hdisc : ∀ E : MMP.Mori.PrimeDivisor Y₀,
      IsDiscrepancy sX₀ n (divisorOfForm ω) B₀ ⟨Y₀, p₀, hY₀, hbir, E⟩ (C.coeff E) :=
    fun E => isDiscrepancy_coeff_divisorOfForm_sub_pullback hP.1 ω hω0 hP.2.1 B₀ hQ p₀ hY₀ hbir E
  have hΔC : ∀ E, -ΔY.coeff E = C.coeff E := fun E => (hΔY E).eq (hdisc E)
  have hC1 : ∀ E, -1 < C.coeff E := fun E => by
    have := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hY₀ hbir hΔY E
    linarith [hΔC E]
  -- `D_Y = p₀^* D = m P`
  have hDZ :
      Divisor.toQDivisor D = ((m : ℕ) : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + B₀) := by
    rw [hDm]; ext E; simp
  obtain ⟨DY, hDY, hDYpb⟩ := QDivisor.isPullback_pullback (f := p₀) hQ hsupp m hm D hDZ hD
  have hDYE : ∀ E, ((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY)).coeff E =
      -(KY.coeff E : ℚ) + C.coeff E := by
    intro E
    have h1 := congrArg (fun F : QDivisor Y₀ => F.coeff E) hDY
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_neg,
      hCdef, DivisorWithCoeffs.coeff_sub, smul_eq_mul, Int.cast_neg, h1]
    field_simp
    ring
  refine ⟨KY, DY,
    MMP.Mori.isCanonicalDivisor_divisorOfForm_pullback hP.1 hω0 hP.2.1 hY₀ hbir hsm,
    ⟨_, hDYpb⟩, ?_, ?_⟩
  · ext E
    rw [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_roundUp, hDYE, DivisorWithCoeffs.coeff_mapCoeffs,
      DivisorWithCoeffs.coeff_neg, hΔC E]
    exact ceil_max_zero_eq_add_ceil _ _ (hC1 E)
  · refine DivisorWithCoeffs.isSNC_of_forall_genericPoint_mem hsm hres.isSNCSubset _ fun E hE => ?_
    refine (hdisc E).genericPoint_mem_of_ne_zero fun h => hE ?_
    change (((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY)).fract).coeff E = 0
    rw [DivisorWithCoeffs.coeff_fract, hDYE, h, add_zero,
      show -((KY.coeff E : ℤ) : ℚ) = ((-KY.coeff E : ℤ) : ℚ) by push_cast; ring]
    exact Int.fract_intCast _

end ResolutionSide

section BaseChangeIntegral

/-- Over the base change `p : Y ⟶ X` of a birational `p₀` along `q`, with `q'` open, the open
`q'⁻¹ U₁` where `p` is an open immersion meets `p⁻¹ U` in a dense open. -/
private theorem exists_dense_isOpenImmersion_morphismRestrict {X₀ Y₀ X Y : Scheme.{0}}
    {p₀ : Y₀ ⟶ X₀} (hp₀ : IsBirationalMorphism p₀) {q : X ⟶ X₀} {q' : Y ⟶ Y₀} {p : Y ⟶ X}
    (H : IsPullback q' p p₀ q) (hq' : IsOpenMap q'.base) (U : X.Opens) :
    ∃ O : (p ⁻¹ᵁ U).toScheme.Opens, Dense (O : Set (p ⁻¹ᵁ U).toScheme) ∧
      IsOpenImmersion (O.ι ≫ (p ∣_ U)) := by
  obtain ⟨U₁, hU₁, hU₁p⟩ := exists_isOpenImmersion_of_isBirationalMorphism hp₀
  -- `p` is an open immersion over `q'⁻¹ U₁`
  have hP : IsPullback (q' ∣_ U₁) ((q' ⁻¹ᵁ U₁).ι ≫ p) (U₁.ι ≫ p₀) q :=
    (isPullback_morphismRestrict q' U₁).paste_vert H
  haveI : IsOpenImmersion ((q' ⁻¹ᵁ U₁).ι ≫ p) := MorphismProperty.of_isPullback hP hU₁p
  refine ⟨(p ⁻¹ᵁ U).ι ⁻¹ᵁ (q' ⁻¹ᵁ U₁), ?_, ?_⟩
  · rw [dense_iff_inter_open]
    rintro W hW ⟨x, hx⟩
    have hWo : IsOpen (q'.base '' ((p ⁻¹ᵁ U).ι.base '' W)) :=
      hq' _ ((p ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap _ hW)
    obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hyU⟩ :=
      hU₁.inter_open_nonempty _ hWo ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
    exact ⟨y, hy, hyU⟩
  · have h1 : ((p ⁻¹ᵁ U).ι ⁻¹ᵁ (q' ⁻¹ᵁ U₁)).ι ≫ (p ⁻¹ᵁ U).ι =
        ((p ⁻¹ᵁ U).ι ∣_ (q' ⁻¹ᵁ U₁)) ≫ (q' ⁻¹ᵁ U₁).ι :=
      (morphismRestrict_ι _ _).symm
    have h2 : (((p ⁻¹ᵁ U).ι ⁻¹ᵁ (q' ⁻¹ᵁ U₁)).ι ≫ (p ∣_ U)) ≫ U.ι =
        ((p ⁻¹ᵁ U).ι ∣_ (q' ⁻¹ᵁ U₁)) ≫ (q' ⁻¹ᵁ U₁).ι ≫ p := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, h1, Category.assoc]
    haveI : IsOpenImmersion ((((p ⁻¹ᵁ U).ι ⁻¹ᵁ (q' ⁻¹ᵁ U₁)).ι ≫ (p ∣_ U)) ≫ U.ι) := by
      rw [h2]; infer_instance
    exact IsOpenImmersion.of_comp _ U.ι

/-- A reduced nonempty scheme with a dense open that embeds openly into an irreducible scheme is
integral, and the morphism is dominant. -/
private theorem isIntegral_and_isDominant_of_isOpenImmersion {Y U : Scheme.{0}} [IrreducibleSpace U]
    [IsReduced Y] [Nonempty Y] (p : Y ⟶ U) (O : Y.Opens) (hO : Dense (O : Set Y))
    [IsOpenImmersion (O.ι ≫ p)] : IsIntegral Y ∧ IsDominant p := by
  have hne : (O : Set Y).Nonempty := hO.nonempty
  obtain ⟨o, ho⟩ := hne
  haveI : Nonempty O := ⟨⟨o, ho⟩⟩
  haveI : IrreducibleSpace O := (O.ι ≫ p).isOpenEmbedding.irreducibleSpace
  have hO' : IsIrreducible (O : Set Y) := by
    have h := (IrreducibleSpace.isIrreducible_univ O).image O.ι.base O.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  haveI : IrreducibleSpace Y := by
    have h := hO'.closure
    rw [hO.closure_eq] at h
    exact (irreducibleSpace_def _).2 h
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced Y, ⟨?_⟩⟩
  have h1 : (Set.range (O.ι ≫ p).base).Nonempty := ⟨_, ⟨o, ho⟩, rfl⟩
  have h2 : Dense (Set.range (O.ι ≫ p).base) :=
    (O.ι ≫ p).isOpenEmbedding.isOpen_range.dense h1
  refine h2.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

end BaseChangeIntegral

section SNCEtale

/-- **Simple normal crossing support transported along an étale morphism.** Let `q : Y' ⟶ Y₀` be
étale, `Y₀` smooth over a perfect field `k` and `T` an snc divisor on `Y₀`. A divisor on `Y'`
each of whose components lies over a component of `T` is snc. -/
private theorem isSNC_of_etale {k : Type} [Field k] [PerfectField k] {Y₀ Y' : Scheme.{0}}
    (s : Y₀ ⟶ Spec (.of k)) [IsLocallyNoetherian Y₀] [TopologicalSpace.NoetherianSpace Y₀]
    (q : Y' ⟶ Y₀) [Etale q]
    [CompactSpace Y'] [LocallyOfFiniteType (q ≫ s)] [Smooth (q ≫ s)]
    {T : Divisor Y₀} (hT : T.IsSNC s) {R : Type*} [Zero R] (D' : DivisorWithCoeffs R Y')
    (h : ∀ E ∈ D'.support, ∃ P ∈ T.support, P.genericPoint = q E.genericPoint) :
    D'.IsSNC (q ≫ s) := by
  classical
  have hS := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC s hT
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = ⋃ F ∈ T.support, (F.support : Set Y₀) := ⟨_, rfl⟩
  rw [← hS₀] at hS
  have hS₀c : IsClosed S₀ := hS.1
  -- the preimage of `S₀` is an snc closed subset
  have hS' : MMP.Resolution.IsSNCClosedSubset (q ≫ s) (q.base ⁻¹' S₀) := by
    obtain ⟨-, h0 | ⟨-, -, hfam⟩⟩ := hS
    · exact ⟨hS₀c.preimage q.continuous, Or.inl (by rw [h0, Set.preimage_empty])⟩
    · refine MMP.Resolution.isSNCClosedSubset_of_forall_isSNCAt (q ≫ s)
        (hS₀c.preimage q.continuous) fun x => ?_
      have hflat : ∀ y, (q.stalkMap y).hom.Flat := fun y => Flat.stalkMap q y
      have hfib := MMP.Resolution.isRegularLocalRing_closedFibre_of_smooth q
      have hfam' := MMP.Resolution.isSNCFamily_comap_of_flat s (q ≫ s) q hflat hfib hfam
      obtain ⟨n, z, c, hz, hc, -⟩ := hfam'.2 x
      obtain ⟨C, hC⟩ := MMP.Resolution.isSNCAt_iUnion_support _ x hc
      refine ⟨n, z, C, hz, ?_⟩
      have hpre : q.base ⁻¹' S₀ = ⋃ i, (((MMP.Resolution.componentsFamily S₀ i).comap q).support :
          Set Y') := by
        conv_lhs => rw [← MMP.Resolution.iUnion_support_componentsFamily hS₀c]
        rw [Set.preimage_iUnion]
        congr 1
        ext i y
        exact (MMP.Resolution.mem_support_comap_iff q _ y).symm
      rw [hpre]
      exact hC
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (q ≫ s)
  refine isSNC_of_isSNCClosedSubset (q ≫ s) hS' D' fun E hE => ?_
  obtain ⟨P, hP, hPE⟩ := h E hE
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine closure_minimal (Set.singleton_subset_iff.2 ?_) (hS₀c.preimage q.continuous)
  change q E.genericPoint ∈ S₀
  rw [← hPE, hS₀]
  exact Set.mem_biUnion hP (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)

end SNCEtale

section Tensor

/-- `Stacks.SheafOfModules.Tensor.sheafTensor` on a scheme, in the spelling of the statement. -/
private abbrev tens (X : Scheme.{0}) (A B : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B

/-- Tensoring with an invertible module is cancellable. -/
private theorem nonempty_iso_of_tens_iso {X : Scheme.{0}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {A B : X.Modules} (e : tens X A L ≅ tens X B L) :
    Nonempty (A ≅ B) := by
  haveI := Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0} ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).flip.obj L)).preimageIso e⟩

/-- Functoriality of the tensor product. -/
private def tensMapIso {X : Scheme.{0}} {A A' B B' : X.Modules} (eA : A ≅ A') (eB : B ≅ B') :
    tens X A B ≅ tens X A' B' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso eA).app B ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj A').mapIso eB

/-- **The pull-back of the ample gap.** If `𝓛^{⊗ m} ≅ q^* N ⊗ 𝓜` and, along `φ`, `φ^* 𝓛 ≅ 𝒪(w_𝓛)`
and `φ^* q^* N ≅ 𝒪(D')`, then `φ^* 𝓜 ≅ 𝒪(m w_𝓛 - D')`. -/
private theorem nonempty_pullback_iso_divisorialSheaf_sub {X X₀ Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (φ : Y ⟶ X) (q : X ⟶ X₀)
    (𝓛 𝓜 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛] [Stacks.Ample.IsInvertibleModule X 𝓜]
    (m : ℕ) (N : X₀.Modules)
    (e : Stacks.Ample.tensorPowModule X 𝓛 (m : ℤ) ≅ tens X ((Scheme.Modules.pullback q).obj N) 𝓜)
    {wL D' : Divisor Y} (hwL : wL.IsCartier) (hD' : D'.IsCartier)
    (ewL : (Scheme.Modules.pullback φ).obj 𝓛 ≅ wL.divisorialSheaf)
    (eD : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback q).obj N) ≅
      D'.divisorialSheaf) :
    Nonempty ((Scheme.Modules.pullback φ).obj 𝓜 ≅ ((m : ℤ) • wL - D').divisorialSheaf) := by
  haveI : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback φ).obj 𝓛) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  haveI := hD'.isInvertibleModule_divisorialSheaf
  obtain ⟨eP⟩ := nonempty_tensorPowModule_iso_divisorialSheaf hwL _ ewL m
  -- `𝒪(m w_𝓛) ≅ 𝒪(D') ⊗ φ^*𝓜`
  have e1 :
      (m • wL).divisorialSheaf ≅ tens Y D'.divisorialSheaf ((Scheme.Modules.pullback φ).obj 𝓜) :=
    eP.symm ≪≫ (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso φ 𝓛 m).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso e ≪≫
        Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso φ _ _ ≪≫ tensMapIso eD (Iso.refl _)
  have hw : ((m : ℤ) • wL - D').IsCartier := (hwL.zsmul _).sub hD'
  have e2 : tens Y ((m : ℤ) • wL - D').divisorialSheaf D'.divisorialSheaf ≅
      (m • wL).divisorialSheaf :=
    hw.divisorialSheafTensorIso hD' ≪≫ eqToIso (by rw [sub_add_cancel, natCast_zsmul])
  exact nonempty_iso_of_tens_iso D'.divisorialSheaf
    (e2 ≪≫ e1 ≪≫ ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding _).app _).app _).symm

/-- The restriction of `q'^* F ⊗ p^* 𝓛` to an open `W`. -/
private def restrictTensorIso {Y Y₀ X : Scheme.{0}} (W : Y.Opens) (q' : Y ⟶ Y₀) (p : Y ⟶ X)
    (𝓛 : X.Modules) (F : Y₀.Modules) :
    (Scheme.Modules.restrictFunctor W.ι).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible Y ((Scheme.Modules.pullback p).obj 𝓛)).obj
        ((Scheme.Modules.pullback q').obj F)) ≅
      tens W ((Scheme.Modules.pullback (W.ι ≫ q')).obj F)
        ((Scheme.Modules.pullback (W.ι ≫ p)).obj 𝓛) :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
    (Scheme.Modules.pullback W.ι).mapIso
      (eqToIso (Stacks.ProjectionFormula.tensorRightInvertible_obj Y _ _)) ≪≫
    Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso W.ι _ _ ≪≫
    tensMapIso ((Scheme.Modules.pullbackComp W.ι q').app F)
      ((Scheme.Modules.pullbackComp W.ι p).app 𝓛)

end Tensor

section Ample

/-- **Restricting a relatively ample sheaf.** If `𝓜` is ample relative to `f : X ⟶ S` and
`U ⊆ f⁻¹ V` is closed in `f⁻¹ V` for an affine open `V ⊆ S`, then `𝓜|_U` is ample. -/
private theorem isAmple_pullback_ι {X S : Scheme.{0}} (f : X ⟶ S) (𝓜 : X.Modules)
    [Stacks.Ample.IsInvertibleModule X 𝓜] (h : Stacks.RelativeAmple.IsRelativelyAmple f 𝓜)
    (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (hUcl : ∀ x ∈ f ⁻¹ᵁ V, x ∈ closure (U : Set X) → x ∈ U) :
    Stacks.Ample.IsAmple U.toScheme ((Scheme.Modules.pullback U.ι).obj 𝓜) := by
  obtain ⟨ι', hι'c, hι'⟩ := exists_isClosedImmersion_lift hUV hUcl
  haveI := hι'c
  have h1 := h.2 V hV
  haveI : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V).toScheme
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj 𝓜) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  have h2 := Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom ι'
    ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj 𝓜) h1
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback U.ι).obj 𝓜) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback ι').obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj 𝓜)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp h2
  exact (Scheme.Modules.pullbackComp ι' (f ⁻¹ᵁ V).ι).app 𝓜 ≪≫
    (Scheme.Modules.pullbackCongr hι').app 𝓜

end Ample

section Piece

/-- **The vanishing module over one integral piece.** Let `U ⊆ f⁻¹ V` be an integral piece,
H-projective over an affine `k`-variety `T` through `π`. On `Y' = p⁻¹ U`, the restriction of
`q'^* 𝒪_{Y₀}(⌈E₀⌉) ⊗ p^* 𝓛` is isomorphic to `𝒪_{Y'}(K_{Y'} + ⌈w/m⌉)`, for `K_{Y'}` the étale
pull-back of a canonical divisor of `Y₀` and `w = m w_𝓛 - q''^* D_Y` the divisor of `p^*(𝓜|_U)`,
and the higher direct images of the latter along `Y' ⟶ U ⟶ T` vanish. -/
private theorem exists_isZero_rightDerived_comp_of_isIntegral
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X₀ : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {n : ℕ} {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : IsKltPair sX₀ n K₀ B₀)
    {S₀ : Scheme.{0}} (f₀ : X₀ ⟶ S₀) (hf₀ : IsProjective f₀)
    {X S : Scheme.{0}} (g : S ⟶ S₀) [Etale g] (q : X ⟶ X₀) (f : X ⟶ S)
    (hpb : IsPullback q f f₀ g)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛]
    (m : ℕ) (hm : 0 < m) (D : Divisor X₀) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K₀ + B₀))
    (𝓜 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓜] (h𝓜 : IsRelativelyAmple f 𝓜)
    (e : Stacks.Ample.tensorPowModule X 𝓛 (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj D.divisorialSheaf)).obj 𝓜)
    {Y₀ : Scheme.{0}} (p₀ : Y₀ ⟶ X₀) (hres : IsLogResolution sX₀ (QDivisor.toRDivisor B₀) p₀)
    (hp₀ : IsProjectiveMorphism p₀) (hY₀ : IsNormalVariety k (p₀ ≫ sX₀))
    {ΔY : QDivisor Y₀}
    (hΔY : IsCrepantBoundary sX₀ n K₀ B₀ p₀ hY₀ hres.isBirationalMorphism ΔY)
    {Y : Scheme.{0}} (q' : Y ⟶ Y₀) (p : Y ⟶ X) (H : IsPullback q' p p₀ q)
    (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (hUcl : ∀ x ∈ f ⁻¹ᵁ V, x ∈ closure (U : Set X) → x ∈ U)
    (hU : IsIntegral U.toScheme)
    (T : Scheme.{0}) (sT : T ⟶ Spec (.of k)) (π : U.toScheme ⟶ T) [IsAffine T]
    (hTv : AlgebraicGeometry.IsVariety k sT) (hπ : IsProjectiveMorphism π)
    (hπs : π ≫ sT = U.ι ≫ q ≫ sX₀) :
    haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
    haveI : IsNormal Y₀ := hY₀.2
    ∃ G : (p ⁻¹ᵁ U).toScheme.Modules, G.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U).ι).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible Y
          ((Scheme.Modules.pullback p).obj 𝓛)).obj ((Scheme.Modules.pullback q').obj
            ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp.divisorialSheaf)) ≅ G) ∧
      ∀ j : ℕ, 0 < j →
        IsZero (((Scheme.Modules.pushforward ((p ∣_ U) ≫ π)).rightDerived j).obj G) := by
  haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
  haveI : IsNormal Y₀ := hY₀.2
  haveI : IsIntegral Y₀ := hY₀.1.toIsIntegral
  haveI : Etale q := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : Etale q' := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : IsProper p₀ := hres.isProper
  haveI : IsProper p := MorphismProperty.of_isPullback H inferInstance
  set Y' := p ⁻¹ᵁ U with hY'
  set p' : Y'.toScheme ⟶ U.toScheme := p ∣_ U with hp'
  set q'' : Y'.toScheme ⟶ Y₀ := Y'.ι ≫ q' with hq''
  haveI : Etale q'' := inferInstance
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπ
  haveI : IsProper f₀ := hf₀.isProper
  haveI : IsProper f := MorphismProperty.of_isPullback hpb inferInstance
  have hbir := hres.isBirationalMorphism
  haveI : IsDominant p₀ := hbir.isDominant
  have hcomp : p' ≫ U.ι ≫ q = q'' ≫ p₀ := by
    rw [← Category.assoc, hp', morphismRestrict_ι, Category.assoc, ← H.w, hq'', Category.assoc]
  have hcomp' : p' ≫ (U.ι ≫ q ≫ sX₀) = q'' ≫ (p₀ ≫ sX₀) := by
    rw [← Category.assoc U.ι, ← Category.assoc, hcomp, Category.assoc]
  -- smoothness, normality
  have hsmY₀ : IsSmoothScheme (p₀ ≫ sX₀) := hres.isSmoothScheme
  haveI : Smooth (p₀ ≫ sX₀) := (isSmoothScheme_iff _).mp hsmY₀
  haveI : Smooth (q'' ≫ p₀ ≫ sX₀) := inferInstance
  have hsmY' : IsSmoothScheme (q'' ≫ p₀ ≫ sX₀) := (isSmoothScheme_iff _).mpr inferInstance
  haveI : IsNormal Y'.toScheme := isNormal_of_etale q''
  haveI : IsLocallyNoetherian Y'.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (q'' ≫ p₀ ≫ sX₀)
  -- nonemptiness
  haveI : Surjective p₀ :=
    surjective_of_isDominant_of_isClosed_range p₀ p₀.isClosedMap.isClosed_range
  haveI : Surjective p := MorphismProperty.of_isPullback H inferInstance
  haveI : Nonempty U.toScheme := inferInstance
  haveI : Nonempty Y'.toScheme := by
    obtain ⟨u⟩ := ‹Nonempty U.toScheme›
    obtain ⟨y, hy⟩ := p.surjective u.1
    exact ⟨⟨y, show p y ∈ U from hy ▸ u.2⟩⟩
  -- `Y'` is integral and `p'` birational
  obtain ⟨O, hO, hOi⟩ := exists_dense_isOpenImmersion_morphismRestrict hbir H q'.isOpenMap U
  obtain ⟨hint, hdom⟩ := isIntegral_and_isDominant_of_isOpenImmersion p' O hO
  have hbirp : IsBirationalMorphism p' := isBirationalMorphism_of_isOpenImmersion p' O hO
  haveI : IsIntegral Y'.toScheme := hint
  haveI : IsDominant p' := hdom
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace π
  haveI : IsProper p' := inferInstance
  haveI : CompactSpace Y'.toScheme := QuasiCompact.compactSpace_of_compactSpace p'
  haveI := hTv
  haveI hvU : AlgebraicGeometry.IsVariety k (U.ι ≫ q ≫ sX₀) := by
    rw [← hπs]; exact {}
  haveI hvY' : AlgebraicGeometry.IsVariety k (p' ≫ (U.ι ≫ q ≫ sX₀)) := by
    rw [← hπs]; exact {}
  have hY' : IsNormalVariety k (q'' ≫ p₀ ≫ sX₀) := ⟨by rw [← hcomp']; exact hvY', inferInstance⟩
  haveI : IsDominant q'' :=
    ⟨(q''.isOpenMap.isOpen_range).dense (Set.range_nonempty _)⟩
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace (p₀ ≫ sX₀)
  -- the data on `Y₀`
  obtain ⟨KY₀, DY₀, hKY₀, ⟨hDB, hDY₀⟩, hR₀, hsnc₀⟩ :=
    exists_canonical_pullback_roundUp sX₀ hklt m hm D hD hDm p₀ hres hY₀ hΔY
  -- pull-backs along the étale `q''`
  have hcart : ∀ G : Divisor Y₀, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY₀
  have hsupp : ∀ G : Divisor Y₀, ∀ Z : irreducibleComponents Y'.toScheme,
      q'' (componentGenericPoint _ Z) ∉ G.supp := fun G =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q'' G
  have hpbG : ∀ G : Divisor Y₀, G.IsPullback q'' (hsupp G) (G.pullback (hcart G) (hsupp G)) :=
    fun G => Divisor.isPullback_pullback (hcart G) (hsupp G)
  choose Pof hPof using MMP.Mori.PrimeDivisor.exists_genericPoint_eq_of_etale q''
  have hcoeff : ∀ (G : Divisor Y₀) (E : MMP.Mori.PrimeDivisor Y'.toScheme),
      (G.pullback (hcart G) (hsupp G)).coeff E = G.coeff (Pof E) := fun G E =>
    Divisor.IsPullback.coeff_eq_of_etale q'' (hcart G) (hpbG G) E (Pof E) (hPof E)
  -- the canonical divisor of `Y'`
  obtain ⟨hK', K', hK'can, -, hK'pb⟩ :=
    Divisor.exists_isCanonicalDivisor_isPullback_of_etale hY₀ q''
    hY' hKY₀ (QDivisor.isQCartier_toQDivisor (hcart KY₀))
  have hK'coeff : ∀ E, K'.coeff E = KY₀.coeff (Pof E) := by
    intro E
    obtain ⟨D', hD', hD'pb⟩ := hK'pb 1 one_pos KY₀ (by simp) (hcart KY₀)
    have : D' = K' := Divisor.toQDivisor_injective (by rw [hD']; simp)
    subst this
    exact Divisor.IsPullback.coeff_eq_of_etale q'' (hcart KY₀) hD'pb E (Pof E) (hPof E)
  -- the divisors `D' = q''^* D_Y` and `R' = q''^* ⌈E₀⌉`
  set R₀ := ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp with hR₀def
  set D' := DY₀.pullback (hcart DY₀) (hsupp DY₀) with hD'def
  set R' := R₀.pullback (hcart R₀) (hsupp R₀) with hR'def
  -- the line bundle `𝓛` on `Y'`
  haveI : IsNoetherian Y₀ := ⟨⟩
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback U.ι).obj 𝓛) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  haveI : Stacks.Ample.IsInvertibleModule Y'.toScheme
      ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback U.ι).obj 𝓛)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  obtain ⟨wL, ⟨ewL⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback U.ι).obj 𝓛))
  set w : Divisor Y'.toScheme := (m : ℤ) • wL - D' with hwdef
  have hwE : ∀ E, ((m : ℚ)⁻¹ • Divisor.toQDivisor w).coeff E =
      (wL.coeff E : ℚ) + ((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY₀)).coeff (Pof E) := by
    intro E
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, hwdef,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg, hD'def, hcoeff, smul_eq_mul,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_neg]
    field_simp
    ring
  have hround : K' + ((m : ℚ)⁻¹ • Divisor.toQDivisor w).roundUp = wL + R' := by
    ext E
    have h1 := congrArg (fun F : Divisor Y₀ => F.coeff (Pof E)) hR₀
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp] at h1
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp, hwE, Int.ceil_intCast_add,
      DivisorWithCoeffs.coeff_add, hR'def, hcoeff, h1, hK'coeff]
    ring
  -- the fractional part is snc
  set F₀ := ((m : ℚ)⁻¹ • Divisor.toQDivisor (-DY₀)).fract with hF₀
  set T₀ : Divisor Y₀ := F₀.mapCoeffs (fun c => if c = 0 then 0 else 1) (by simp) with hT₀
  have hT₀s : T₀.IsSNC (p₀ ≫ sX₀) := hsnc₀.of_support_subset fun P hP => by
    rw [Finsupp.mem_support_iff] at hP ⊢
    intro h0
    apply hP
    change T₀.coeff P = 0
    rw [hT₀, DivisorWithCoeffs.coeff_mapCoeffs]
    exact if_pos h0
  have hsncY' : ((m : ℚ)⁻¹ • Divisor.toQDivisor w).fract.IsSNC (q'' ≫ p₀ ≫ sX₀) := by
    refine isSNC_of_etale (p₀ ≫ sX₀) q'' hT₀s _ fun E hE => ⟨Pof E, ?_, hPof E⟩
    rw [Finsupp.mem_support_iff] at hE ⊢
    change ¬ T₀.coeff (Pof E) = 0
    rw [hT₀, DivisorWithCoeffs.coeff_mapCoeffs, ite_eq_left_iff, not_forall]
    refine ⟨fun h0 => hE ?_, one_ne_zero⟩
    change Int.fract (((m : ℚ)⁻¹ • Divisor.toQDivisor w).coeff E) = 0
    rw [hwE, Int.fract_intCast_add]
    exact h0
  -- `p'^*(𝓜|_U) ≅ 𝒪(w)`
  have hcartY' : ∀ G : Divisor Y'.toScheme, G.IsCartier :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsmY'
  have eD : (Scheme.Modules.pullback (p' ≫ U.ι)).obj
      ((Scheme.Modules.pullback q).obj D.divisorialSheaf) ≅ D'.divisorialSheaf :=
    (Scheme.Modules.pullbackComp (p' ≫ U.ι) q).app _ ≪≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hcomp])).app _ ≪≫
      ((Scheme.Modules.pullbackComp q'' p₀).app _).symm ≪≫
      (Scheme.Modules.pullback q'').mapIso (Divisor.IsPullback.divisorialSheafIso (hBc := hD)
        hDY₀).symm ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hcart DY₀) (hpbG DY₀)).symm
  obtain ⟨ew₀⟩ := nonempty_pullback_iso_divisorialSheaf_sub (p' ≫ U.ι) q 𝓛 𝓜 m
    D.divisorialSheaf e (hcartY' wL) (hcartY' D')
    (((Scheme.Modules.pullbackComp p' U.ι).app 𝓛).symm ≪≫ ewL.symm) eD
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback U.ι).obj 𝓜) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  have ew : (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback U.ι).obj 𝓜) ≅
      w.divisorialSheaf := (Scheme.Modules.pullbackComp p' U.ι).app 𝓜 ≪≫ ew₀
  -- `𝓜|_U` is ample relative to `π`
  have h𝓜s : Stacks.RelativeAmple.IsRelativelyAmple f 𝓜 :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f 𝓜
      inferInstance h𝓜
  have h𝓐 : Stacks.RelativeAmple.IsRelativelyAmple π ((Scheme.Modules.pullback U.ι).obj 𝓜) :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple π _).2
      (isAmple_pullback_ι f 𝓜 h𝓜s V hV U hUV hUcl)
  -- `p'` is projective
  have hP' : IsPullback ((p ⁻¹ᵁ U).ι ≫ q') (p ∣_ U) p₀ (U.ι ≫ q) :=
    (isPullback_morphismRestrict p U).flip.paste_horiz H
  have hp'proj : IsProjectiveMorphism p' := by
    obtain ⟨N, i, hi, hif⟩ := hp₀.baseChange (U.ι ≫ q)
    refine ⟨N, hP'.isoPullback.hom ≫ i, inferInstance, ?_⟩
    rw [Category.assoc, hif, IsPullback.isoPullback_hom_snd]
  -- the vanishing
  have hvan := fun j hj =>
    MMP.Fourfold.isZero_rightDerived_pushforward_comp_roundUp_of_pullback_iso
      (U.ι ≫ q ≫ sX₀) sT π hπs hπ p'
      (by rw [hcomp']; exact hsmY') hp'proj hbirp (by rw [hcomp']; exact hK'can) m hm
      ((Scheme.Modules.pullback U.ι).obj 𝓜) h𝓐 w ew (by rw [hcomp']; exact hsncY') j hj
  refine ⟨(K' + ((m : ℚ)⁻¹ • Divisor.toQDivisor w).roundUp).divisorialSheaf, inferInstance,
    ⟨?_⟩, hvan⟩
  have eR : (Scheme.Modules.pullback (Y'.ι ≫ q')).obj R₀.divisorialSheaf ≅ R'.divisorialSheaf :=
    (Divisor.IsPullback.divisorialSheafIso (hBc := hcart R₀) (hpbG R₀)).symm
  have eL : (Scheme.Modules.pullback (Y'.ι ≫ p)).obj 𝓛 ≅ wL.divisorialSheaf :=
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι p U).symm).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp p' U.ι).app 𝓛).symm ≪≫ ewL.symm
  exact restrictTensorIso Y' q' p 𝓛 R₀.divisorialSheaf ≪≫ tensMapIso eR eL ≪≫
    (hcartY' R').divisorialSheafTensorIso (hcartY' wL) ≪≫ eqToIso (by rw [hround, add_comm])

end Piece

section Main

/-- **The vanishing over one integral piece.** For an affine open `V ⊆ S` and an integral open
`U ⊆ f⁻¹ V`, the cohomology of `𝒩 ⊗ p^*𝓛` over `p⁻¹ U` vanishes in positive degrees. -/
private theorem isZero_Hgroup_preimage_of_isIntegral
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X₀ : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {n : ℕ} {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : IsKltPair sX₀ n K₀ B₀)
    {S₀ : Scheme.{0}} (sS₀ : S₀ ⟶ Spec (.of k)) (f₀ : X₀ ⟶ S₀) (hfs : f₀ ≫ sS₀ = sX₀)
    (hf₀ : IsProjective f₀)
    {X S : Scheme.{0}} (g : S ⟶ S₀) [Etale g] (q : X ⟶ X₀) (f : X ⟶ S)
    (hpb : IsPullback q f f₀ g)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛]
    (m : ℕ) (hm : 0 < m) (D : Divisor X₀) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K₀ + B₀))
    (𝓜 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓜] (h𝓜 : IsRelativelyAmple f 𝓜)
    (e : Stacks.Ample.tensorPowModule X 𝓛 (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj D.divisorialSheaf)).obj 𝓜)
    {Y₀ : Scheme.{0}} (p₀ : Y₀ ⟶ X₀) (hres : IsLogResolution sX₀ (QDivisor.toRDivisor B₀) p₀)
    (hp₀ : IsProjectiveMorphism p₀) (hY₀ : IsNormalVariety k (p₀ ≫ sX₀))
    {ΔY : QDivisor Y₀}
    (hΔY : IsCrepantBoundary sX₀ n K₀ B₀ p₀ hY₀ hres.isBirationalMorphism ΔY)
    {Y : Scheme.{0}} (q' : Y ⟶ Y₀) (p : Y ⟶ X) (H : IsPullback q' p p₀ q)
    (i : ℕ) (hi : 0 < i) (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (hUcl : ∀ x ∈ f ⁻¹ᵁ V, x ∈ closure (U : Set X) → x ∈ U)
    (hU : IsIntegral U.toScheme) :
    haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
    haveI : IsNormal Y₀ := hY₀.2
    IsZero (Hgroup Y.ringCatSheaf (p ⁻¹ᵁ U) i
      ((Stacks.ProjectionFormula.tensorRightInvertible Y ((Scheme.Modules.pullback p).obj 𝓛)).obj
        ((Scheme.Modules.pullback q').obj
          ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp.divisorialSheaf))) := by
  haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
  haveI : IsNormal Y₀ := hY₀.2
  haveI : IsProper f₀ := hf₀.isProper
  obtain ⟨T, sT, π, hTa, hTv, hπ, hπs⟩ :=
    exists_isProjectiveMorphism_isAffine_of_le_preimage sX₀ sS₀ f₀ hfs g q f hpb V hV U hUV
      hUcl hU
  haveI := hTa
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπ
  haveI : IsProper p₀ := hres.isProper
  haveI : IsProper p := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨G, hG, ⟨eG⟩, hvan⟩ := exists_isZero_rightDerived_comp_of_isIntegral sX₀ hklt f₀
    hf₀ g q f hpb 𝓛 m hm D hD hDm 𝓜 h𝓜 e p₀ hres hp₀ hY₀ hΔY q' p H V hV U hUV hUcl hU T sT π
    hTv hπ hπs
  exact isZero_Hgroup_of_isZero_rightDerived_of_isAffine (p ⁻¹ᵁ U) ((p ∣_ U) ≫ π) _ G eG hvan i hi

/-- **Relative Kawamata–Viehweg vanishing on the étale base change of the resolution.** -/
private theorem isZero_rightDerived_comp_tensor_pullback_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X₀ : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {n : ℕ} {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : IsKltPair sX₀ n K₀ B₀)
    {S₀ : Scheme.{0}} (sS₀ : S₀ ⟶ Spec (.of k)) (f₀ : X₀ ⟶ S₀) (hfs : f₀ ≫ sS₀ = sX₀)
    (hf₀ : IsProjective f₀)
    {X S : Scheme.{0}} (g : S ⟶ S₀) [Etale g] (q : X ⟶ X₀) (f : X ⟶ S)
    (hpb : IsPullback q f f₀ g)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛]
    (m : ℕ) (hm : 0 < m) (D : Divisor X₀) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K₀ + B₀))
    (𝓜 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓜] (h𝓜 : IsRelativelyAmple f 𝓜)
    (e : Stacks.Ample.tensorPowModule X 𝓛 (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj D.divisorialSheaf)).obj 𝓜)
    {Y₀ : Scheme.{0}} (p₀ : Y₀ ⟶ X₀) (hres : IsLogResolution sX₀ (QDivisor.toRDivisor B₀) p₀)
    (hp₀ : IsProjectiveMorphism p₀) (hY₀ : IsNormalVariety k (p₀ ≫ sX₀))
    {ΔY : QDivisor Y₀}
    (hΔY : IsCrepantBoundary sX₀ n K₀ B₀ p₀ hY₀ hres.isBirationalMorphism ΔY)
    {Y : Scheme.{0}} (q' : Y ⟶ Y₀) (p : Y ⟶ X) (H : IsPullback q' p p₀ q)
    (i : ℕ) (hi : 0 < i) :
    haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
    haveI : IsNormal Y₀ := hY₀.2
    IsZero (((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible Y ((Scheme.Modules.pullback p).obj 𝓛)).obj
        ((Scheme.Modules.pullback q').obj
          ((-ΔY).mapCoeffs (max · 0) (by simp)).roundUp.divisorialSheaf))) := by
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard S.Modules
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (Scheme.Modules.pushforward (p ≫ f)) (rfl : (i : ℤ) = (i : ℤ)) _).1 ?_
  refine
    Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
      (p ≫ f) _ i S.isBasis_affineOpens fun V hV => ?_
  haveI : IsProper f₀ := hf₀.isProper
  haveI : IsProper f := MorphismProperty.of_isPullback hpb inferInstance
  haveI : Etale q := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : IsNormal X := isNormal_of_etale q
  obtain ⟨ι, t, U, hd, hsup, hU⟩ := exists_finset_pairwiseDisjoint_isIntegral (f ⁻¹ᵁ V)
    (QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV.isCompact)
  have hpre : (p ≫ f) ⁻¹ᵁ V = t.sup fun c => p ⁻¹ᵁ U c := by
    rw [Scheme.Hom.comp_preimage, ← hsup]
    exact map_finset_sup (TopologicalSpace.Opens.comap p.base.hom) t U
  rw [hpre]
  refine isZero_Hgroup_finsetSup t _ ?_ _ i fun c hc =>
    isZero_Hgroup_preimage_of_isIntegral sX₀ hklt sS₀ f₀ hfs hf₀ g q f hpb 𝓛 m hm D hD hDm 𝓜
      h𝓜 e p₀ hres hp₀ hY₀ hΔY q' p H i hi V hV (U c) (hsup ▸ Finset.le_sup hc)
      (mem_of_mem_closure_of_pairwiseDisjoint t U hd hsup hc) (hU c)
  intro a ha b hb hab
  exact Disjoint.map (f := TopologicalSpace.Opens.comap p.base.hom) (hd ha hb hab)

end Main

end

end MMP.FourfoldProofs.FourfoldEtaleProjectiveKltAmpleVanishingProof

end

section

/-!
# Ample-gap klt vanishing after an étale base change

Let `(X₀, B₀)` be a klt pair with `B₀` an effective `ℚ`-divisor and `X₀` a projective variety
over an algebraically closed field `k` of characteristic zero, and let `f₀ : X₀ ⟶ S₀` be a
projective morphism of `k`-schemes. Let `g : S ⟶ S₀` be étale and let `X = X₀ ×_{S₀} S`, with
projections `q : X ⟶ X₀` and `f : X ⟶ S`; the pair `(X, B)` has `K_X + B = q^*(K_{X₀} + B₀)`.
If `𝓛 = 𝒪_X(A)` is a line bundle on `X` such that `A - (K_X + B)` is `f`-ample, then
`R^i f_* 𝓛 = 0` for every `i > 0`.

The proof base-changes a projective log resolution `Y₀ ⟶ X₀` of the global pair along `q`,
uses `R p_* 𝒪_Y(E) = 𝒪_X` for the exceptional divisor `E = -⌊B_Y⌋` (klt log-resolution
vanishing and flat base change), and applies relative round-up vanishing for the pull-back of
the relatively ample divisor `A - (K_X + B)` to `𝒪_Y(p^*A + E) = 𝒪_Y(K_Y + ⌈p^*(A - K_X - B)⌉)`.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_of_isPullback_etale_of_isKltPair`: the
  vanishing above.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero.
* The étale base change "on an open of `S₀`" is an étale morphism `g : S ⟶ S₀`: an étale
  morphism to an open `U ⊆ S₀` composed with the inclusion is étale, and every étale morphism
  factors through its open image. The source pair is a cartesian square
  `CategoryTheory.IsPullback q f f₀ g` rather than the chosen fibre product.
* `X` need not be integral, so the Cartier divisor `A` is recorded as its line bundle `𝓛`
  (`Stacks.Ample.IsInvertibleModule`) and `K_X + B` as the pull-back along `q` of
  `K_{X₀} + B₀`. Since `K_{X₀} + B₀` is `ℚ`-Cartier, "`A - (K_X + B)` is `f`-ample" means: for
  some `m > 0` with `m (K_{X₀} + B₀) = D` a Cartier divisor, there is an `f`-ample line bundle
  `𝓜` (`MMP.Mori.IsRelativelyAmple`) with `𝓛^{⊗ m} ≅ q^* 𝒪_{X₀}(D) ⊗ 𝓜`.
* `R^i f_*` is the `i`-th right derived functor of `AlgebraicGeometry.Scheme.Modules.pushforward`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.70,
  Thm. 5.22
-/

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open CategoryTheory.Limits MMP.FourfoldProofs
  MMP.FourfoldProofs.FourfoldEtaleProjectiveKltAmpleVanishingProof in
/-- **Ample-gap klt vanishing after an étale base change.** Let `(X₀, B₀)` be a klt pair, with
`B₀` effective and `X₀` projective over an algebraically closed field `k` of characteristic zero,
and `f₀ : X₀ ⟶ S₀` a projective morphism of `k`-schemes. Let `g : S ⟶ S₀` be étale and
`X = X₀ ×_{S₀} S` with projections `q` and `f`. Let `𝓛` be a line bundle on `X`, `m > 0` and
`D` a Cartier divisor on `X₀` with `D = m (K_{X₀} + B₀)`, and suppose
`𝓛^{⊗ m} ≅ q^* 𝒪_{X₀}(D) ⊗ 𝓜` for an `f`-ample line bundle `𝓜`. Then `R^i f_* 𝓛 = 0` for
every `i > 0`. -/
@[mmp "lem_fourfold_etale_projective_klt_ample_vanishing"]
public theorem isZero_rightDerived_pushforward_of_isPullback_etale_of_isKltPair
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X₀ : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    (sX₀ : X₀ ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX₀]
    {n : ℕ} {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : MMP.Mori.IsKltPair sX₀ n K₀ B₀)
    (hB₀ : 0 ≤ B₀)
    {S₀ : Scheme.{0}} (sS₀ : S₀ ⟶ Spec (.of k)) (f₀ : X₀ ⟶ S₀) (hfs : f₀ ≫ sS₀ = sX₀)
    (hf₀ : IsProjective f₀)
    {X S : Scheme.{0}} (g : S ⟶ S₀) [Etale g] (q : X ⟶ X₀) (f : X ⟶ S)
    (hpb : IsPullback q f f₀ g)
    (𝓛 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓛]
    (m : ℕ) (hm : 0 < m) (D : Divisor X₀) (hD : D.IsCartier)
    (hDm : Divisor.toQDivisor D = (m : ℚ) • (Divisor.toQDivisor K₀ + B₀))
    (𝓜 : X.Modules) [Stacks.Ample.IsInvertibleModule X 𝓜] (h𝓜 : IsRelativelyAmple f 𝓜)
    (e : Stacks.Ample.tensorPowModule X 𝓛 (m : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback q).obj D.divisorialSheaf)).obj 𝓜)
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj 𝓛) := by
  -- a projective log resolution `p₀ : Y₀ ⟶ X₀` of the global pair
  obtain ⟨Y₀, p₀, hres, hp₀⟩ := exists_isLogResolution_isProjectiveMorphism sX₀ hklt.1.1
    (QDivisor.toRDivisor B₀)
  have hY₀ : IsNormalVariety k (p₀ ≫ sX₀) :=
    (hres.toIsSmoothResolution.isNormalVariety hklt.1.1).1
  haveI : IsLocallyNoetherian Y₀ := hY₀.1.isLocallyNoetherian
  haveI : IsNormal Y₀ := hY₀.2
  haveI : IsProper p₀ := hres.isProper
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hklt.1.isPair
    hklt.1.2.1 p₀ hY₀ hres.isBirationalMorphism
  have hB := hΔY.isDiscrepancyPositivePart hklt.1
  set E₀ : QDivisor Y₀ := (-ΔY).mapCoeffs (max · 0) (by simp) with hE₀
  -- `R^j p₀_* 𝒪(⌈E₀⌉) = 0` and `p₀_* 𝒪(⌈E₀⌉) = 𝒪_{X₀}`
  have hvan := isZero_rightDerived_pushforward_divisorialSheaf_roundUp sX₀ hklt hB₀ p₀ hres
    hp₀.isProjective hY₀ hB
  obtain ⟨h0, hφ⟩ := isIso_pushforward_structureSheafToDivisorialSheaf_roundUp sX₀ hB₀ p₀ hY₀
    hres.isBirationalMorphism hB
  -- the étale base change `p : Y ⟶ X`
  haveI : Etale q := MorphismProperty.of_isPullback hpb.flip inferInstance
  have H : IsPullback (Limits.pullback.fst p₀ q) (Limits.pullback.snd p₀ q) p₀ q :=
    IsPullback.of_hasPullback p₀ q
  set N := (Scheme.Modules.pullback (Limits.pullback.fst p₀ q)).obj E₀.roundUp.divisorialSheaf
  have hN : ∀ j : ℕ, 0 < j → IsZero (((Scheme.Modules.pushforward
      (Limits.pullback.snd p₀ q)).rightDerived j).obj N) := fun j hj =>
    isZero_rightDerived_pushforward_of_isPullback H _ j (hvan j hj)
  have eN := pushforwardPullbackIsoUnit H E₀.roundUp.divisorialSheaf
    (asIso (SheafOfModules.unitToPushforwardObjUnit p₀.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward p₀).map (Divisor.structureSheafToDivisorialSheaf h0))).symm
  exact isZero_rightDerived_pushforward_of_comp_tensor_pullback (Limits.pullback.snd p₀ q) f N hN
    eN 𝓛 i (isZero_rightDerived_comp_tensor_pullback_roundUp sX₀ hklt sS₀ f₀ hfs hf₀ g q f
      hpb 𝓛 m hm D hD hDm 𝓜 h𝓜 e p₀ hres hp₀ hY₀ hΔY _ _ H i hi)

end MMP.Fourfold

end
