module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistStalkVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackCovering.Basic

/-!
# Basic results of Kollár–Mori, Chapters 0 and 1

This file states the basic well-definedness and positivity results of Kollár–Mori used in the
three-dimensional minimal model program: intersection numbers of `ℚ`-Cartier divisors can be
computed with any Cartier multiple, nonnegativity of mixed intersection numbers against an ample
sheaf, the easy direction of Nakai–Moishezon, the leading term of the Snapper polynomial, and
ampleness near a fibre (KM Proposition 1.41).

## Main results

* `MMP.Threefold.Mori.isInvertibleModule_divisorialSheaf_of_toQDivisor_eq_smul`: `𝒪_X(mD)` is
  invertible when `mD` is Cartier; with `MMP.Mori.QDivisor.intersectionNumber_eq_of_smul`,
  `(D · C) = (1 / m) deg_C 𝒪_X(mD)`.
* `MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple`: `(L^j M^{d-j} · Z) ≥ 0` for every
  closed subscheme `Z` of dimension at most `d`, when `L` has nonnegative degree on every
  `j`-dimensional subvariety and `M` is ample; with
  `MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple_of_forall_eq_or_eq`, the form for a
  family of slots each equal to `L` or `M`.
* `MMP.Threefold.Mori.sheafPowIntersectionNumber_nonneg_of_isAmple`: `(L^j · M^{n-j}) ≥ 0`
  when `L` has nonnegative degree on every `j`-dimensional subvariety and `M` is ample.
* `MMP.Threefold.Mori.exists_isZero_stalk_rightDerived_twistModule_of_isAmple_fiber`:
  eventual vanishing of `(R^i f_* ℱ(νD))_y` (the claim `(∗)` of KM Proposition 1.41).
* `MMP.Threefold.Mori.exists_isAmpleOver_of_isAmple_fiber`: KM Proposition 1.41.
* `MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple`: KM Theorem 1.37 (⇒).
* `MMP.Threefold.Mori.eval_homogeneousComponent_of_eulerChar`,
  `MMP.Threefold.Mori.exists_eulerChar_eq_selfIntersection_div_factorial_add`: KM Theorem 1.36,
  second clause.

The following statements are registered on declarations already in the library:
`MMP.Mori.Divisor.IsLocalEquation.exists_unit_stalk` (a local equation is a unit off the
support), `MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback` (existence and uniqueness of
`f^*B`) and `MMP.Mori.QDivisor.intersectionNumber_eq_of_smul`.

## Implementation notes

The results of KM Chapter 1 stated for Cartier divisors on arbitrary proper schemes are stated
for invertible sheaves `L` (the sheaves `𝒪_X(D)` of the source); invertibility is carried in the
two spellings the intersection number (`SheafOfModules.IsInvertible`) and ampleness
(`Stacks.Ample.IsInvertibleModule`) use. Nefness is defined for `ℝ`-Cartier divisors, so
KM Theorem 1.38 is stated for a Cartier divisor `L : X.CartierDivisor` and its sheaf. A closed
integral subscheme `Z ⊆ X` is a closed immersion `i : Z ⟶ X` from an integral scheme.

The fibre `X_y` is `f.fiber y` with its morphism `f.fiberι y` to `X`; the hypothesis that
`𝒪_{X_y}(D)` is ample is that the pull-back of `L` to the fibre is ample.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4,
  Remark 1.26, Theorems 1.36–1.38, Proposition 1.41
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Mori

open MMP.Mori

/-! ### Auxiliary: the signed intersection number agrees with the Stacks one -/

section Aux

open MvPolynomial

section Twist

open Stacks.SheafOfModules.Invertible

/-- The Euler-characteristic sum of the pulled-back twist of the sheaf of `D` along `𝟙 X` is that
of `𝒪_X((∑ a) D)`. -/
private theorem eulerSum_twistedSheaf_pullbackId (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.CartierDivisor) (n : ℕ) (a : Fin n → ℤ) (j : ℕ) :
    Module.finrank k (cohomologyOverField k (𝟙 X ≫ f)
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun _ : Fin n => (Scheme.Modules.pullback (𝟙 X)).obj
          (MMP.CartierDivisor.sheaf D)) a) j) =
    Module.finrank k (cohomologyOverField k f
      (MMP.CartierDivisor.sheaf ((∑ i, a i) • D)) j) := by
  set M := MMP.CartierDivisor.sheaf D
  have e1 : twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun _ : Fin n => (Scheme.Modules.pullback (𝟙 X)).obj M) a ≅
      tensorPower X.presheaf X.ringCatSheaf.2 M (∑ i, a i) :=
    MMP.Mori.Twist.twistedSheafUnitIsoTensorPower _ M
      (fun _ => (Scheme.Modules.pullbackId X).app M) a
  obtain ⟨e2'⟩ := MMP.Resolution.Bridges.cartierSheaf_sum_iso_twistedSheaf
    (fun _ : Fin 1 => D) (fun _ => ∑ i, a i)
  have e3 := MMP.Mori.Twist.twistedSheafUnitIsoTensorPower (fun _ : Fin 1 => M) M
    (fun _ => Iso.refl _)
    (fun _ => ∑ i, a i)
  have h2 : (∑ _i : Fin 1, ∑ i, a i) = ∑ i, a i := by simp
  have e2 : MMP.CartierDivisor.sheaf ((∑ i, a i) • D) ≅
      tensorPower X.presheaf X.ringCatSheaf.2 M (∑ i, a i) :=
    eqToIso (by simp) ≪≫ e2' ≪≫ e3 ≪≫ eqToIso (by rw [h2])
  rw [Category.id_comp]
  exact finrank_cohomologyOverField_eq_of_iso k f (e1 ≪≫ e2.symm) j

end Twist

/-- The polynomial `Q(a) = P((∑ a) • m)` in `n` variables attached to `P` and a vector `m`. -/
private noncomputable def sumSubstMv {r : ℕ} (n : ℕ) (m : Fin r → ℚ) (P : MvPolynomial (Fin r) ℚ) :
    MvPolynomial (Fin n) ℚ :=
  ∑ s ∈ P.support, C (P.coeff s * ∏ i, m i ^ s i) * (∑ j : Fin n, X j) ^ (s.degree)

private theorem eval_sumSubstMv {r : ℕ} (n : ℕ) (m : Fin r → ℚ) (P : MvPolynomial (Fin r) ℚ)
    (a : Fin n → ℚ) :
    eval a (sumSubstMv n m P) = eval (fun i => m i * ∑ j, a j) P := by
  rw [sumSubstMv, map_sum, eval_eq']
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [map_mul, eval_C, map_pow, map_sum, eval_X, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum]
  ring

private theorem totalDegree_sumSubstMv {r : ℕ} (n : ℕ) (m : Fin r → ℚ)
    (P : MvPolynomial (Fin r) ℚ) :
    (sumSubstMv n m P).totalDegree ≤ P.totalDegree := by
  classical
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun s hs => ?_)
  refine le_trans (totalDegree_mul _ _) ?_
  have hA : (∑ i : Fin n, X i : MvPolynomial (Fin n) ℚ).totalDegree ≤ 1 :=
    le_trans (totalDegree_finsetSum _ _)
      (Finset.sup_le fun i _ => le_of_eq (totalDegree_X i))
  have h2 : ((∑ i : Fin n, X i : MvPolynomial (Fin n) ℚ) ^ s.degree).totalDegree ≤ s.degree :=
    le_trans (totalDegree_pow _ _) (by simpa using Nat.mul_le_mul_left s.degree hA)
  have h1 : (C (P.coeff s * ∏ i, m i ^ s i) : MvPolynomial (Fin n) ℚ).totalDegree = 0 :=
    totalDegree_C _
  have h3 : s.degree ≤ P.totalDegree := le_totalDegree hs
  omega

private theorem coeff_sumSubstMv {r : ℕ} (n : ℕ) (m : Fin r → ℚ) (P : MvPolynomial (Fin r) ℚ) :
    (sumSubstMv n m P).coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin n => 1) =
      n.factorial * eval m (homogeneousComponent n P) := by
  classical
  set e : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin n => 1
  have hmval : ∀ i, e i = 1 := fun i => rfl
  have hsum : (e.sum fun _ e => e) = n := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp [hmval]
  have hmult : e.multinomial = n.factorial := by
    rw [Finsupp.multinomial, Finsupp.sum_fintype _ _ (fun _ => rfl),
      Finsupp.prod_fintype _ _ (fun _ => rfl)]
    simp [hmval]
  rw [sumSubstMv, coeff_sum, homogeneousComponent_apply, map_sum, Finset.mul_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeff_sum_X_pow_of_fintype, hsum, hmult, eval_monomial,
    Finsupp.prod_fintype _ _ (by simp)]
  by_cases h : s.degree = n
  · simp [h]
    ring
  · simp [h, Ne.symm h]

private theorem cast_finsum_int (g : ℕ → ℤ) : ((∑ᶠ j, g j : ℤ) : ℚ) = ∑ᶠ j, (g j : ℚ) :=
  (Int.castAddHom ℚ).map_finsum_of_injective Int.cast_injective g

/-- The self-intersection number of `𝒪_X(D)` is the coefficient of `a₁ ⋯ aₙ` in any polynomial of
total degree at most `n` taking the Euler characteristics `χ(X, 𝒪_X((∑ aⱼ) D))` as its values. -/
private theorem sheafSelfIntersectionNumber_cartier_eq_coeff (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (D : X.CartierDivisor) (n : ℕ)
    (hn : topologicalKrullDim X ≤ n) (Q : MvPolynomial (Fin n) ℚ) (hQ : Q.totalDegree ≤ n)
    (hv : ∀ a : Fin n → ℤ, eval (fun j => (a j : ℚ)) Q =
      ((∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
        (MMP.CartierDivisor.sheaf ((∑ i, a i) • D)) j) : ℤ)) : ℚ)) :
    (sheafSelfIntersectionNumber k f (𝟙 X) n hn (MMP.CartierDivisor.sheaf D) : ℚ) =
      Q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  unfold sheafSelfIntersectionNumber
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine AlgebraicGeometry.intersectionNumber_eq_coeff k f (𝟙 X) n hn
    (fun _ => MMP.CartierDivisor.sheaf D) Q (fun a => ?_) hQ
  rw [hv a, AlgebraicGeometry.eulerCharacteristic_eq_finsum, cast_finsum_int]
  refine finsum_congr fun j => ?_
  rw [eulerSum_twistedSheaf_pullbackId k f D n a j]
  push_cast
  rfl

end Aux

/-! ### Mixed intersection numbers against an ample sheaf -/

section Mixed

open AlgebraicGeometry
open Stacks.SheafOfModules.Invertible (tensorPower)

/-- Nonnegativity of an intersection number from nonnegativity on the top-dimensional
components, as `AlgebraicGeometry.intersectionNumber_pos_of_pos_topDimComponents`. -/
private theorem intersectionNumber_nonneg_of_nonneg_topDimComponents (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (hnn : ∀ W : TopDimIntegralSubscheme
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        0 ≤ intersectionNumber k f W.1.subschemeι d
          (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme i hd W) L) :
    0 ≤ intersectionNumber k f i d hd.le L := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hZcoh : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hFcoh : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  have : Finite (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
    finite_topDimIntegralSubscheme k f _
  classical
  haveI : Fintype (TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) := Fintype.ofFinite _
  rw [intersectionNumber_eq_sum_topDimComponents k f i d hd L, finsum_eq_sum_of_fintype]
  exact Finset.sum_nonneg fun W _ =>
    mul_nonneg (sheafMultiplicity_genericPt_pos k f _ W).le (hnn W)

/-- A top-dimensional integral component of a closed subscheme `Z` of dimension `d` has
dimension `d`. -/
theorem topologicalKrullDim_subscheme_eq_of_topDimIntegralSubscheme {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {d : ℕ} (hd : topologicalKrullDim Z = (d : WithBot ℕ∞))
    (W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :
    topologicalKrullDim W.1.subscheme = (d : WithBot ℕ∞) :=
  W.2.2.2.trans (by rwa [Stacks.Chow.supp_pushforwardStructureSheaf i,
    topologicalKrullDim_range_eq i])

/-- **Cutting by a divisor of an ample sheaf.** Let `W ⊆ X` be a closed integral subscheme of
dimension `d + 1` and `G` a family of `d + 1` invertible sheaves with `G₀` ample. If
`(G₁ ⋯ G_d · D) ≥ 0` for every closed subscheme `D ⊆ X` of dimension `d`, then
`(G₀ ⋯ G_d · W) ≥ 0`. -/
theorem intersectionNumber_nonneg_of_isAmple_zero (k : Type u) [Field k] {X W : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (ι : W ⟶ X) [IsClosedImmersion ι] [IsIntegral W] (d : ℕ)
    (hdim : topologicalKrullDim W = ((d + 1 : ℕ) : WithBot ℕ∞)) (G : Fin (d + 1) → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (G q)]
    (hG : Stacks.Ample.IsAmple X (G 0))
    (hT : ∀ {D : Scheme.{u}} (j : D ⟶ X) [IsClosedImmersion j]
      (hD : topologicalKrullDim D = (d : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f j d hD.le fun t => G t.succ) :
    0 ≤ intersectionNumber k f ι (d + 1) hdim.le G := by
  have hposdim : 0 < topologicalKrullDim W := by
    rw [hdim]
    exact_mod_cast Nat.succ_pos d
  have hMample : Scheme.Modules.IsAmple W ((Scheme.Modules.pullback ι).obj (G 0)) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        ι (G 0) hG (Or.inl ⟨inferInstance, inferInstance⟩))
  obtain ⟨n, D, hn, hDcartier, hDne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k (ι ≫ f) hposdim
      ((Scheme.Modules.pullback ι).obj (G 0)) hMample
  have : Nonempty D.subscheme := hDne
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hDcartier
  have hDdim : topologicalKrullDim D.subscheme = (d : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (ι ≫ f) D hDcartier hdim
  set N : Fin (d + 1) → X.Modules :=
    Function.update G 0 (tensorPower X.presheaf X.ringCatSheaf.2 (G 0) (n : ℤ))
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
    isInvertible_update G 0 _
  have hNiso : (Scheme.Modules.pullback ι).obj (N 0) ≅
      (Stacks.Divisors.invertibleSheaf D : W.Modules) :=
    eqToIso (congrArg (Scheme.Modules.pullback ι).obj
        (Function.update_self (0 : Fin (d + 1)) _ G)) ≪≫
      Scheme.Modules.pullbackTensorPowerIso ι (G 0) n ≪≫ e
  have hNnn : 0 ≤ intersectionNumber k f ι (d + 1) hdim.le N := by
    rw [intersectionNumber_eq_of_isEffectiveCartierDivisor k f ι d hdim.le N D hDdim.le hNiso,
      intersectionNumber_congr_family k f _ d _
        (funext fun t => Function.update_of_ne (Fin.succ_ne_zero t) _ _ :
          (fun t : Fin d => N t.succ) = fun t => G t.succ)]
    exact hT (D.subschemeι ≫ ι) hDdim
  rw [intersectionNumber_update_tensorPower k f ι (d + 1) hdim.le G 0 n] at hNnn
  exact nonneg_of_mul_nonneg_right hNnn (by exact_mod_cast hn)

/- The proof follows that of [Stacks, Tag 0BEV] in `AlgebraicGeometry.intersectionNumber_pos`, by
induction on the number of slots of `M`: the number is a positive combination of its values on
the top-dimensional components `W` of `Z`; on such `W` a power `M^{⊗ n}` has an effective Cartier
divisor `D`, and cutting by `D` removes one slot of `M` and one dimension. -/
/-- **Mixed intersection numbers against an ample sheaf are nonnegative** (KM Theorem 1.38,
proof). Let `X` be proper over `k`, `L` and `M` invertible sheaves on `X` with `M` ample, and
suppose `(L^j · W) ≥ 0` for every closed integral subscheme `W ⊆ X` of dimension `j`. Then for
every closed subscheme `Z ⊆ X` of dimension at most `d` and every family `F` of `d` sheaves
equal to `M` in the slots of a set `S` of `d - j` slots and to `L` in the others,
`(F₁ ⋯ F_d · Z) = (L^j M^{d-j} · Z) ≥ 0`. -/
theorem intersectionNumber_nonneg_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple X M) (j : ℕ)
    (hL : ∀ (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
      (hW : topologicalKrullDim W = (j : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f i j hW.le (fun _ => L))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (F : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)] (S : Finset (Fin d))
    (hSM : ∀ q ∈ S, F q = M) (hSL : ∀ q ∉ S, F q = L) (hj : j + S.card = d) :
    0 ≤ intersectionNumber k f i d hd F := by
  classical
  rcases hd.lt_or_eq with hlt | hdim
  · exact (intersectionNumber_eq_zero_of_topologicalKrullDim_lt k f i d hd hlt F).ge
  obtain ⟨s, hs⟩ : ∃ s, S.card = s := ⟨_, rfl⟩
  induction s generalizing d Z i F S with
  | zero =>
    obtain rfl : j = d := by omega
    refine intersectionNumber_nonneg_of_nonneg_topDimComponents k f i j hdim _ (fun W => ?_)
    have : IsIntegral W.1.subscheme := W.2.1
    rw [intersectionNumber_congr_family k f W.1.subschemeι _ _
      (funext fun q => hSL q (by simp [Finset.card_eq_zero.1 hs]))]
    exact hL W.1.subscheme W.1.subschemeι
      (topologicalKrullDim_subscheme_eq_of_topDimIntegralSubscheme i hdim W)
  | succ s ih =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨j + s, by omega⟩
    obtain ⟨q0, hq0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    let σ : Equiv.Perm (Fin (d' + 1)) := Equiv.swap 0 q0
    rw [← intersectionNumber_comp_perm k f i (d' + 1) hd F σ]
    set S' : Finset (Fin d') := Finset.univ.filter fun t => σ t.succ ∈ S
    have hcard : S.card = S'.card + 1 := by
      have h := Equiv.sum_comp σ fun q => if q ∈ S then 1 else 0
      rw [Fin.sum_univ_succ] at h
      simp [σ, hq0] at h
      exact h.symm.trans (add_comm _ _)
    refine intersectionNumber_nonneg_of_nonneg_topDimComponents k f i (d' + 1) hdim _
      (fun W => ?_)
    have : IsIntegral W.1.subscheme := W.2.1
    exact intersectionNumber_nonneg_of_isAmple_zero k f W.1.subschemeι d'
      (topologicalKrullDim_subscheme_eq_of_topDimIntegralSubscheme i hdim W) _
      (by simpa [σ, hSM q0 hq0] using hM)
      fun j' _ hD => ih j' d' hD.le _ S' (fun t ht => hSM _ (Finset.mem_filter.1 ht).2)
        (fun t ht => hSL _ fun h => ht (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
        (by omega) hD (by omega)

/-- **Mixed intersection numbers of a nef and an ample sheaf are nonnegative.** Let `X` be
proper over `k`, `L` and `M` invertible sheaves on `X` with `M` ample, and suppose
`(L^j · W) ≥ 0` for every `j` and every closed integral subscheme `W ⊆ X` of dimension `j`
(e.g. `L` nef). Then `(F₁ ⋯ F_d · Z) ≥ 0` for every closed subscheme `Z ⊆ X` of dimension at most
`d` and every family `F` of `d` sheaves each equal to `L` or to `M`. -/
theorem intersectionNumber_nonneg_of_isAmple_of_forall_eq_or_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hM : Stacks.Ample.IsAmple X M)
    (hL : ∀ (j : ℕ) (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
      (hW : topologicalKrullDim W = (j : WithBot ℕ∞)),
      0 ≤ intersectionNumber k f i j hW.le (fun _ => L))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (F : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)]
    (hF : ∀ q, F q = L ∨ F q = M) : 0 ≤ intersectionNumber k f i d hd F := by
  classical
  set S : Finset (Fin d) := Finset.univ.filter fun q => F q ≠ L
  have hS : S.card ≤ d := (Finset.card_le_univ S).trans_eq (Fintype.card_fin d)
  exact intersectionNumber_nonneg_of_isAmple k f L M hM (d - S.card) (hL _) i d hd F S
    (fun q hq => (hF q).resolve_left (Finset.mem_filter.1 hq).2)
    (fun q hq => by simpa [S] using hq) (by omega)

end Mixed

/-! ### Kollár–Mori, Notation 0.4 -/

section Notation

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **`𝒪_X(mD)` is invertible.** Let `X` be a normal scheme of finite type over `k`, `D` a
`ℚ`-Cartier `ℚ`-divisor on `X` and `m > 0` such that `mD` is a Cartier divisor `E`. Then
`𝒪_X(mD) = 𝒪_X(E)` is invertible. The second assertion of the lemma,
`(D · C) = (1 / m) deg_C 𝒪_X(mD)`, is `MMP.Mori.QDivisor.intersectionNumber_eq_of_smul`. -/
@[mmp "lem_km0_intersection_number_any_multiple"]
theorem isInvertibleModule_divisorialSheaf_of_toQDivisor_eq_smul (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (D : QDivisor X)
    (_hD : D.IsQCartier) {m : ℕ} (_hm : 0 < m) (E : Divisor X) (hE : E.IsCartier)
    (_h : Divisor.toQDivisor E = (m : ℤ) • D) :
    Stacks.Ample.IsInvertibleModule X E.divisorialSheaf := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  exact hE.isInvertibleModule_divisorialSheaf

attribute [mmp "lem_km0_intersection_number_any_multiple"]
  MMP.Mori.QDivisor.intersectionNumber_eq_of_smul

attribute [mmp "lem_km0_local_equation_unit_off_support"]
  MMP.Mori.Divisor.IsLocalEquation.exists_unit_stalk

attribute [mmp "lem_km0_pullback_q_cartier_exists_unique"]
  MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback

end Notation

/-! ### Intersection numbers: Kollár–Mori, Theorems 1.36–1.38 -/

section Intersection

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **Mixed degrees against an ample divisor are nonnegative** (KM Theorem 1.38, proof). Let `X`
be a projective variety of dimension `n`, `L` an invertible sheaf, `M` an ample invertible sheaf
on `X` and `0 ≤ j ≤ n`. If `(L^j · W) ≥ 0` for every closed integral subscheme `W ⊆ X` of
dimension `j`, then `(L^j · M^{n-j}) ≥ 0`. -/
@[mmp "lem_km1b_nef_mixed_degree_nonnegative"]
theorem sheafPowIntersectionNumber_nonneg_of_isAmple (hX : MMP.Mori.IsProjectiveVariety k f)
    {n : ℕ} (hn : topologicalKrullDim X = n) (L M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [Stacks.Ample.IsInvertibleModule X M] (hM : Stacks.Ample.IsAmple X M) {j : ℕ} (hj : j ≤ n)
    (hL : ∀ (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
      (hW : topologicalKrullDim W = j), 0 ≤ sheafSelfIntersectionNumber k f i j hW.le L) :
    haveI : ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![L, M] t) := by
      intro t
      fin_cases t <;> assumption
    0 ≤ sheafPowIntersectionNumber k f (𝟙 X) ![j, n - j]
      (by rw [hn]; exact_mod_cast (show n ≤ ∑ t, ![j, n - j] t by simp; omega)) ![L, M] := by
  classical
  have hjn : (∑ t, ![j, n - j] t) = n := by simp [Fin.sum_univ_two]; omega
  have hinv : ∀ t : Fin 2, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (![L, M] t) := by
    intro t
    fin_cases t <;> assumption
  have : ∀ t : Fin (∑ t, ![j, n - j] t), SheafOfModules.IsInvertible X.presheaf
      X.ringCatSheaf.2 (![L, M] (finSigmaFinEquiv.symm t).1) := fun t => hinv _
  unfold sheafPowIntersectionNumber
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_nonneg_of_isAmple k f L M hM j (fun W i _ _ hW => ?_) (𝟙 X) _ _ _
    (Finset.univ.filter fun t => (finSigmaFinEquiv.symm t).1 = 1) (fun t ht => ?_)
    (fun t ht => ?_) ?_
  · have h := hL W i hW
    unfold sheafSelfIntersectionNumber at h
    rwa [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber] at h
  · rw [(Finset.mem_filter.1 ht).2]
    rfl
  · have ht : (finSigmaFinEquiv.symm t).1 ≠ 1 := by simpa using ht
    generalize (finSigmaFinEquiv.symm t).1 = a at ht ⊢
    fin_cases a <;> simp_all
  · rw [Finset.card_filter, Equiv.sum_comp (finSigmaFinEquiv.symm : Fin (∑ t, ![j, n - j] t) ≃
        (Σ a : Fin 2, Fin (![j, n - j] a))) (fun σ => if σ.1 = 1 then 1 else 0),
      Fintype.sum_sigma, Fin.sum_univ_two, hjn]
    change j + ((∑ _b : Fin j, if (0 : Fin 2) = 1 then 1 else 0) +
      ∑ _b : Fin (n - j), if (1 : Fin 2) = 1 then 1 else 0) = n
    simp
    omega

/-- **Nakai–Moishezon, the easy direction** (KM Theorem 1.37 (⇒)). Let `X` be a proper scheme
and `L` an ample invertible sheaf on `X`. Then `(L^{dim Z} · Z) > 0` for every closed integral
subscheme `Z ⊆ X`. -/
@[mmp "thm_km1b_nakai_moishezon_ample_implies_positive"]
theorem sheafSelfIntersectionNumber_pos_of_isAmple (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ)
    (hd : topologicalKrullDim Z = d) :
    0 < sheafSelfIntersectionNumber k f i d hd.le L := by
  unfold sheafSelfIntersectionNumber
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact AlgebraicGeometry.selfIntersectionNumber_pos k f i d hd L
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL)

/-- The Euler characteristic `χ(X, 𝒪_X(∑ᵢ mᵢ Lᵢ))` of a combination of Cartier divisors, written
as the alternating sum of the dimensions of the cohomology groups, as in
`MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum`. -/
def eulerCharCartierCombination {r : ℕ} (L : Fin r → X.CartierDivisor) (m : Fin r → ℤ) : ℤ :=
  ∑ᶠ j : ℕ, (-1 : ℤ) ^ j * (Module.finrank k (cohomologyOverField k f
    (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) j) : ℤ)

/-- **Very weak Riemann–Roch, the leading term** (KM Theorem 1.36). Let `X` be a proper scheme of
dimension `n`, `L₁, …, L_r` Cartier divisors on `X` and `P` the polynomial with
`P(m) = χ(X, 𝒪_X(∑ᵢ mᵢ Lᵢ))` for all `m ∈ ℤʳ`. Then its homogeneous part `P_n` of degree `n`
satisfies `P_n(m) = ((∑ᵢ mᵢ Lᵢ)ⁿ) / n!` for every `m ∈ ℤʳ`. -/
@[mmp "thm_km1b_very_weak_riemann_roch_leading_term"]
theorem eval_homogeneousComponent_of_eulerChar {n : ℕ} (hn : topologicalKrullDim X = n)
    {r : ℕ} (L : Fin r → X.CartierDivisor) (P : MvPolynomial (Fin r) ℚ)
    (hP : ∀ m : Fin r → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) P =
      eulerCharCartierCombination k f L m)
    (m : Fin r → ℤ) :
    MvPolynomial.eval (fun i => (m i : ℚ)) (MvPolynomial.homogeneousComponent n P) =
      (sheafSelfIntersectionNumber k f (𝟙 X) n hn.le
        (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) : ℚ) / n.factorial := by
  obtain ⟨P0, hdeg, hP0⟩ := MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum
    k f n hn L
  have hPP0 : P = P0 := MvPolynomial.eq_of_eval_intCast_eq (fun m => by
    rw [hP m, hP0 m, eulerCharCartierCombination, cast_finsum_int]
    push_cast
    rfl)
  subst hPP0
  set D : X.CartierDivisor := ∑ i, m i • L i with hD
  have hkey := sheafSelfIntersectionNumber_cartier_eq_coeff k f D n hn.le
    (sumSubstMv n (fun i => (m i : ℚ)) P) ((totalDegree_sumSubstMv n _ P).trans hdeg) (fun a => by
      rw [eval_sumSubstMv]
      have h1 : ((∑ i, a i) • D : X.CartierDivisor) = ∑ i, ((∑ j, a j) * m i) • L i := by
        rw [hD, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      have h2 : (fun i => (m i : ℚ) * ∑ j, (a j : ℚ)) =
          fun i => (((∑ j, a j) * m i : ℤ) : ℚ) := by
        funext i
        push_cast
        ring
      rw [h1, h2]
      exact hP0 _)
  rw [hkey, coeff_sumSubstMv]
  field_simp

/-- **Very weak Riemann–Roch** (KM Theorem 1.36), the reformulation:
`χ(X, 𝒪_X(∑ᵢ mᵢ Lᵢ)) = ((∑ᵢ mᵢ Lᵢ)ⁿ) / n! + Q(m)` for a polynomial `Q` of degree `< n`. -/
@[mmp "thm_km1b_very_weak_riemann_roch_leading_term"]
theorem exists_eulerChar_eq_selfIntersection_div_factorial_add {n : ℕ}
    (hn : topologicalKrullDim X = n) {r : ℕ} (L : Fin r → X.CartierDivisor) :
    ∃ Q : MvPolynomial (Fin r) ℚ, (Q = 0 ∨ Q.totalDegree < n) ∧
      ∀ m : Fin r → ℤ, (eulerCharCartierCombination k f L m : ℚ) =
        (sheafSelfIntersectionNumber k f (𝟙 X) n hn.le
          (MMP.CartierDivisor.sheaf (∑ i, m i • L i)) : ℚ) / n.factorial +
        MvPolynomial.eval (fun i => (m i : ℚ)) Q := by
  obtain ⟨P, hdeg, hP⟩ := MMP.Resolution.Bridges.exists_polynomial_eulerChar_cartierSheaf_sum
    k f n hn L
  have hP' : ∀ m : Fin r → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) P =
      eulerCharCartierCombination k f L m := fun m => by
    rw [hP m, eulerCharCartierCombination, cast_finsum_int]
    push_cast
    rfl
  refine ⟨P - MvPolynomial.homogeneousComponent n P, ?_, fun m => ?_⟩
  · by_cases h0 : P - MvPolynomial.homogeneousComponent n P = 0
    · exact Or.inl h0
    · right
      obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.2 h0
      have hlt : ∀ s ∈ (P - MvPolynomial.homogeneousComponent n P).support, s.degree < n := by
        intro s hs
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub,
          MvPolynomial.coeff_homogeneousComponent] at hs
        by_cases h : s.degree = n
        · simp [h] at hs
        · simp only [h, ite_false, sub_zero] at hs
          have : s.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree
            (MvPolynomial.mem_support_iff.2 hs)
          omega
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (hlt s hs)
      exact (Finset.sup_lt_iff (by exact_mod_cast hn0)).2 hlt
  · rw [map_sub, ← hP' m, eval_homogeneousComponent_of_eulerChar k f hn L P hP' m]
    ring

end Intersection

/-! ### Ampleness near a fibre: Kollár–Mori, Proposition 1.41 -/

section Fibre

open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (twistModule)

private theorem isIso_res_ofLE {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens) (W : Y.Opens)
    (hle : f ⁻¹ᵁ W ≤ V) : IsIso (V.ι ∣_ (f ⁻¹ᵁ W)) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  exact ⟨⟨⟨x.1, hle x.2⟩, x.2⟩, Subtype.ext <|
    congrArg (fun h => h ⟨⟨x.1, hle x.2⟩, x.2⟩) (morphismRestrict_ι V.ι (f ⁻¹ᵁ W))⟩

private theorem isProper_res_ofLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (V : X.Opens)
    (W : Y.Opens) (hle : f ⁻¹ᵁ W ≤ V) : IsProper ((V.ι ≫ f) ∣_ W) := by
  rw [morphismRestrict_comp]
  have := isIso_res_ofLE f V W hle
  exact MorphismProperty.RespectsIso.precomp (@IsProper) (V.ι ∣_ (f ⁻¹ᵁ W)) _
    (inferInstance : IsProper (f ∣_ W))

private theorem isZero_stalk_rightDerived_of_restrict_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (y : Y) (hy : y ∈ W) (p : ℕ)
    (T : X.Modules) (T0 : (g ⁻¹ᵁ W).toScheme.Modules)
    (e : (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ W).ι).obj T ≅ T0)
    (h : IsZero ((((Scheme.Modules.pushforward (g ∣_ W)).rightDerived p).obj T0).presheaf.stalk
      (⟨y, hy⟩ : W.toScheme))) :
    IsZero ((((Scheme.Modules.pushforward g).rightDerived p).obj T).presheaf.stalk y) := by
  set y' : W.toScheme := ⟨y, hy⟩
  set A := ((Scheme.Modules.pushforward g).rightDerived p).obj T
  let e2 : ((Scheme.Modules.pushforward (g ∣_ W)).rightDerived p).obj T0 ≅
      (Scheme.Modules.restrictFunctor W.ι).obj A :=
    (((Scheme.Modules.pushforward (g ∣_ W)).rightDerived p).mapIso e).symm ≪≫
      (AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictIsoScheme g W p).app T
  have h1 : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y').obj
      ((Scheme.Modules.toPresheaf W.toScheme).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj A))) := by
    have h' : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y').obj
      ((Scheme.Modules.toPresheaf W.toScheme).obj
        (((Scheme.Modules.pushforward (g ∣_ W)).rightDerived p).obj T0))) := h
    exact h'.of_iso ((TopCat.Presheaf.stalkFunctor Ab.{u} y').mapIso
      ((Scheme.Modules.toPresheaf W.toScheme).mapIso e2)).symm
  exact h1.of_iso ((Scheme.Modules.restrictStalkNatIso W.ι y').app A).symm

/-- If `L` is ample on the fibre `X_y` of `f`, then its pullback is ample on the fibre over `y` of
the restriction of `V.ι ≫ f` to any open `W ∋ y`. -/
theorem isAmple_fiber_morphismRestrict_of_isAmple_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : X.Modules) [IsInvertibleModule X L] (y : Y)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) (V : X.Opens) (W : Y.Opens)
    [IsProper ((V.ι ≫ f) ∣_ W)] (hyW : y ∈ W) :
    IsAmple (((V.ι ≫ f) ∣_ W).fiber ⟨y, hyW⟩) (pullbackModule (((V.ι ≫ f) ∣_ W).fiberι ⟨y, hyW⟩)
      (pullbackModule ((V.ι ≫ f) ⁻¹ᵁ W).ι (pullbackModule V.ι L))) := by
  let y0 : W.toScheme := ⟨y, hyW⟩
  have hcomm : (((V.ι ≫ f) ∣_ W).fiberι y0 ≫ ((V.ι ≫ f) ⁻¹ᵁ W).ι ≫ V.ι) ≫ f =
      ((V.ι ≫ f) ∣_ W).fiberToSpecResidueField y0 ≫ (Spec.map (W.ι.residueFieldMap y0) ≫
        Y.fromSpecResidueField y) := by
    have e : Spec.map (W.ι.residueFieldMap y0) ≫ Y.fromSpecResidueField y =
        W.toScheme.fromSpecResidueField y0 ≫ W.ι :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField W.ι y0
    rw [e]
    calc _ = Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0 ≫ (((V.ι ≫ f) ⁻¹ᵁ W).ι ≫ V.ι ≫ f) := by simp
      _ = Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0 ≫ (((V.ι ≫ f) ∣_ W) ≫ W.ι) := by
        rw [morphismRestrict_ι]
      _ = _ := by rw [← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc]
  let q : ((V.ι ≫ f) ∣_ W).fiber y0 ⟶ f.fiber y :=
    pullback.lift (Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0 ≫ ((V.ι ≫ f) ⁻¹ᵁ W).ι ≫ V.ι)
      (((V.ι ≫ f) ∣_ W).fiberToSpecResidueField y0 ≫ Spec.map (W.ι.residueFieldMap y0))
      (by simp only [Category.assoc]; exact hcomm)
  have hq : q ≫ f.fiberι y = Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0 ≫ ((V.ι ≫ f) ⁻¹ᵁ W).ι ≫ V.ι :=
    pullback.lift_fst _ _ _
  have hemb : Topology.IsEmbedding q := by
    have h1 : Topology.IsEmbedding (⇑(q ≫ f.fiberι y)) := by
      rw [hq]
      exact V.ι.isOpenEmbedding.isEmbedding.comp
        (((V.ι ≫ f) ⁻¹ᵁ W).ι.isOpenEmbedding.isEmbedding.comp
          (Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0).isEmbedding)
    exact Topology.IsEmbedding.of_comp q.continuous (f.fiberι y).continuous h1
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp
    (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
      q (pullbackModule (f.fiberι y) L) hL (Or.inr (Or.inr (Or.inr ⟨inferInstance, hemb⟩))))
  refine ((Scheme.Modules.pullbackComp q (f.fiberι y)).app L) ≪≫ ?_
  refine eqToIso (by rw [hq]) ≪≫ ?_
  refine ((Scheme.Modules.pullbackComp (Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0)
    (((V.ι ≫ f) ⁻¹ᵁ W).ι ≫ V.ι)).app L).symm ≪≫ ?_
  exact (Scheme.Modules.pullback (Scheme.Hom.fiberι ((V.ι ≫ f) ∣_ W) y0)).mapIso
    ((Scheme.Modules.pullbackComp ((V.ι ≫ f) ⁻¹ᵁ W).ι V.ι).app L).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
  (y : Y)

/-- **Eventual vanishing near a fibre** (KM Proposition 1.41, claim `(∗)`). Let `f : X ⟶ Y` be
proper, `L` an invertible sheaf on `X` (the sheaf `𝒪_X(D)` of a Cartier divisor) and `y ∈ Y` such
that `L` is ample on the fibre `X_y`. Then for every coherent sheaf `ℱ` on an open neighbourhood
`V` of `f⁻¹(y)` there is `ν₀` such that `(R^i f_* ℱ(νD))_y = 0` for all `i > 0` and `ν ≥ ν₀`,
where `ℱ(νD) = ℱ ⊗ L^{⊗ ν}`. The base is locally Noetherian, as in the standing convention of
KM §1 (schemes of finite type over a field). -/
@[mmp "lem_km1b_relative_vanishing_near_fibre"]
theorem exists_isZero_stalk_rightDerived_twistModule_of_isAmple_fiber
    [IsLocallyNoetherian Y] (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L))
    (V : X.Opens) (hV : ∀ x : X, f x = y → x ∈ V) (F : V.toScheme.Modules) [F.IsCoherent] :
    ∃ ν₀ : ℕ, ∀ ν : ℕ, ν₀ ≤ ν → ∀ i : ℕ, 0 < i →
      IsZero ((((Scheme.Modules.pushforward (V.ι ≫ f)).rightDerived i).obj
        (twistModule V (pullbackModule V.ι L) F ν)).presheaf.stalk y) := by
  have hcl : IsClosed (f '' (V : Set X)ᶜ) := f.isClosedMap _ V.isOpen.isClosed_compl
  let W : Y.Opens := ⟨(f '' (V : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hyW : y ∈ W := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hV x rfl)
  have hle : f ⁻¹ᵁ W ≤ V := fun x hx => by_contra fun h => hx ⟨x, h, rfl⟩
  have : IsProper ((V.ι ≫ f) ∣_ W) := isProper_res_ofLE f V W hle
  let y0 : W.toScheme := ⟨y, hyW⟩
  let L1 : V.toScheme.Modules := pullbackModule V.ι L
  let L0 := pullbackModule ((V.ι ≫ f) ⁻¹ᵁ W).ι L1
  let F0 := (Scheme.Modules.pullback ((V.ι ≫ f) ⁻¹ᵁ W).ι).obj F
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F0.IsCoherent := AlgebraicGeometry.isCoherent_pullback _ F
  have hamp := isAmple_fiber_morphismRestrict_of_isAmple_fiber f L y hL V W hyW
  obtain ⟨d₀, hd₀⟩ := Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_twistModule
    ((V.ι ≫ f) ∣_ W) y0 F0 L0 hamp
  refine ⟨d₀.toNat, fun ν hν i hi => ?_⟩
  refine isZero_stalk_rightDerived_of_restrict_iso (V.ι ≫ f) W y hyW i _ (twistModule _ L0 F0 ν) ?_
    (hd₀ ν ((Int.self_le_toNat d₀).trans (by exact_mod_cast hν)) i hi)
  exact (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistModuleIso _ L1 F ν

/-- **Ample on a fibre implies ample nearby** (KM Proposition 1.41). Let `f : X ⟶ Y` be a proper
morphism, `L` an invertible sheaf on `X` (the sheaf `𝒪_X(D)` of a Cartier divisor) and `y ∈ Y`
such that `L` is ample on the fibre `X_y`. Then there is an open `U ∋ y` such that `L` is ample
over `U`. -/
@[mmp "prop_km1b_ample_on_fibre_ample_nearby"]
theorem exists_isAmpleOver_of_isAmple_fiber
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ U : Y.Opens, y ∈ U ∧ IsAmpleOver f L U := by
  obtain ⟨V, hyV, hV⟩ :=
    Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f L y hL
  exact ⟨V, hyV, IsRelativelyAmple.of_stacks _ _ hV⟩

end Fibre

end MMP.Threefold.Mori
