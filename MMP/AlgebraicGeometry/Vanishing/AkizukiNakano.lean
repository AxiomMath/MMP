module

public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Vanishing.LogDeligneIllusie
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbers
import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.VectorBundleIso
import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.ArithmeticPoints
import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FiniteTypeModel
import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.WittLift
import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Degreewise
import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenCharacterisation
import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage

/-!
# Akizuki--Nakano vanishing for the negative of an ample line bundle

Let `X` be a smooth projective variety of dimension `n` over a field `k` of characteristic zero
(for instance `k = ℂ`), and let `L` be an ample invertible sheaf on `X`. The Akizuki--Nakano
vanishing theorem, in its negative form, says that

  `H^q(X, Ω_X^a ⊗ L^{-1}) = 0` whenever `a + q < n`.

The proof follows Deligne--Illusie: over a perfect field of characteristic `p > n` with a lift of
`X` to `W₂`, the Frobenius splitting of the de Rham complex gives the dimension inequality
`∑_{a+q=k} h^q(Ω^a ⊗ L^{-1}) ≤ ∑_{a+q=k} h^q(Ω^a ⊗ L^{-p})`; iterating and combining Serre duality
with Serre vanishing gives the result in positive characteristic, and spreading out gives it in
characteristic zero.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_dualSheaf_of_isAmple`:
  `H^q(X, Ω_X^a ⊗ L^{-1}) = 0` for `a + q < n`.

## Implementation notes

* `H^q(X, ℱ)` for `q : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree
  zero, a `k`-vector space; it agrees with sheaf cohomology for `q ≥ 0` and vanishes for `q < 0`,
  so the statement is made for every integer `q`.
* `Ω_X^a = ⋀^a Ω_{X/k}` is `Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a`,
  `L^{-1}` is the dual `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L`, and `⊗` is
  `Stacks.SheafOfModules.Tensor.sheafTensor`; ampleness is `Stacks.Ample.IsAmple`.
* The source works over `ℂ`; the statement is made over an arbitrary field of characteristic
  zero, of which `ℂ` is an instance.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*]
  [DeligneIllusie1987]
* [S. Akizuki, S. Nakano, *Note on Kodaira--Spencer's proof of Lefschetz theorems*]
  [AkizukiNakano1954]
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

/-- `H^j(X, G)`, the cohomology over the base field of a module placed in degree zero. -/
private abbrev H {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (G : X.Modules)
    (j : ℤ) : ModuleCat.{u} k :=
  Stacks.Duality.derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj G) j

/-- `Ω^a_{X/S} ⊗ M`. -/
private abbrev formsTensor {X S : Scheme.{u}} (f : X ⟶ S) (a : ℕ) (M : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)).obj M

/-! ### Counting cohomology groups -/

section Counting

/-- In an exact sequence `A → B → C` of abelian groups with `A` and `C` finite, `B` is finite
and `#B ≤ #A · #C`. -/
private theorem finite_and_card_le_mul_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (φ : A →+ B) (ψ : B →+ C) (h : ∀ b, ψ b = 0 ↔ b ∈ φ.range) [Finite A]
    [Finite C] : Finite B ∧ Nat.card B ≤ Nat.card A * Nat.card C := by
  have hker : ψ.ker = φ.range := AddSubgroup.ext h
  have e := QuotientAddGroup.quotientKerEquivRange ψ
  haveI : Finite φ.range := (Set.finite_range φ).to_subtype
  haveI : Finite ψ.ker := hker ▸ inferInstance
  haveI : Finite (B ⧸ ψ.ker) := Finite.of_equiv _ e.toEquiv.symm
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  haveI : Finite B := by
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  refine ⟨inferInstance, ?_⟩
  rw [hc, mul_comm]
  refine Nat.mul_le_mul ?_ ?_
  · rw [hker]
    exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  · rw [Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The counting bound for an exact short complex of modules. -/
private theorem finite_and_card_le_mul_of_shortComplex_exact {R : Type*} [Ring R]
    (S : ShortComplex (ModuleCat R)) (hS : S.Exact) [Finite S.X₁] [Finite S.X₃] :
    Finite S.X₂ ∧ Nat.card S.X₂ ≤ Nat.card S.X₁ * Nat.card S.X₃ :=
  finite_and_card_le_mul_of_exact S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom fun b =>
    ⟨fun hb => (ShortComplex.moduleCat_exact_iff S).1 hS b hb,
      fun ⟨a, ha⟩ => by
        rw [← ha]
        exact congrArg (fun φ => φ.hom a) S.zero⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The counting bound on a distinguished triangle.** For a distinguished triangle
`K₁ → K₂ → K₃ → K₁[1]` of `D(𝒪_X)` and every `j`, if `H^j(X, K₁)` and `H^j(X, K₃)` are finite
then so is `H^j(X, K₂)`, with `#H^j(X, K₂) ≤ #H^j(X, K₁) · #H^j(X, K₃)`. -/
private theorem finite_and_card_le_mul_of_distinguished
    (T : Pretriangulated.Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules)) (j : ℤ)
    [Finite (Stacks.Duality.derivedCohomologyOverField f T.obj₁ j)]
    [Finite (Stacks.Duality.derivedCohomologyOverField f T.obj₃ j)] :
    Finite (Stacks.Duality.derivedCohomologyOverField f T.obj₂ j) ∧
      Nat.card (Stacks.Duality.derivedCohomologyOverField f T.obj₂ j) ≤
        Nat.card (Stacks.Duality.derivedCohomologyOverField f T.obj₁ j) *
          Nat.card (Stacks.Duality.derivedCohomologyOverField f T.obj₃ j) := by
  have hS := (derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).map_distinguished_exact T hT
  haveI : Finite ((Pretriangulated.shortComplexOfDistTriangle T hT).map
      (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j)).X₁ :=
    ‹Finite (Stacks.Duality.derivedCohomologyOverField f T.obj₁ j)›
  haveI : Finite ((Pretriangulated.shortComplexOfDistTriangle T hT).map
      (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j)).X₃ :=
    ‹Finite (Stacks.Duality.derivedCohomologyOverField f T.obj₃ j)›
  exact finite_and_card_le_mul_of_shortComplex_exact _ hS

end Counting

/-! ### The stupid filtration -/

section Trunc

open ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/-- The stupid truncation `σ^{≥ i} Y` of a cochain complex: `Y^m` in degrees `m ≥ i`, zero
below. -/
private noncomputable def stupidGE (Y : CochainComplex C ℤ) (i : ℤ) : CochainComplex C ℤ where
  X m := if i ≤ m then Y.X m else 0
  d m m' := if h : i ≤ m ∧ i ≤ m' then
      eqToHom (if_pos h.1) ≫ Y.d m m' ≫ eqToHom (if_pos h.2).symm else 0
  shape m m' hmm' := by
    by_cases h : i ≤ m ∧ i ≤ m'
    · rw [dif_pos h, Y.shape _ _ hmm', zero_comp, comp_zero]
    · rw [dif_neg h]
  d_comp_d' m m' m'' _ _ := by
    by_cases h₁ : i ≤ m
    · by_cases h₂ : i ≤ m'
      · by_cases h₃ : i ≤ m''
        · rw [dif_pos ⟨h₁, h₂⟩, dif_pos ⟨h₂, h₃⟩]
          simp
        · rw [dif_neg (show ¬(i ≤ m' ∧ i ≤ m'') from fun h => h₃ h.2), comp_zero]
      · rw [dif_neg (show ¬(i ≤ m ∧ i ≤ m') from fun h => h₂ h.2), zero_comp]
    · rw [dif_neg (show ¬(i ≤ m ∧ i ≤ m') from fun h => h₁ h.1), zero_comp]

private lemma stupidGE_X_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i ≤ m) :
    (stupidGE Y i).X m = Y.X m := if_pos h

private lemma isZero_stupidGE_X_of_lt (Y : CochainComplex C ℤ) {i m : ℤ} (h : m < i) :
    IsZero ((stupidGE Y i).X m) := by
  change IsZero (if i ≤ m then Y.X m else 0)
  rw [if_neg (by omega)]
  exact isZero_zero C

private lemma stupidGE_d (Y : CochainComplex C ℤ) {i m m' : ℤ} (h : i ≤ m) (h' : i ≤ m') :
    (stupidGE Y i).d m m' =
      eqToHom (stupidGE_X_of_le Y h) ≫ Y.d m m' ≫ eqToHom (stupidGE_X_of_le Y h').symm :=
  dif_pos ⟨h, h'⟩

/-- The inclusion `σ^{≥ i} Y ⟶ Y`. -/
private noncomputable def stupidGEι (Y : CochainComplex C ℤ) (i : ℤ) : stupidGE Y i ⟶ Y where
  f m := if h : i ≤ m then eqToHom (stupidGE_X_of_le Y h) else 0
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    by_cases h₁ : i ≤ m
    · rw [dif_pos h₁, dif_pos (by omega : i ≤ m + 1), stupidGE_d Y h₁ (by omega)]
      simp
    · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

private lemma stupidGEι_f_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i ≤ m) :
    (stupidGEι Y i).f m = eqToHom (stupidGE_X_of_le Y h) := dif_pos h

/-- The inclusion `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y`. -/
private noncomputable def stupidGEMap (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGE Y (i + 1) ⟶ stupidGE Y i where
  f m := if h : i + 1 ≤ m then
      eqToHom (stupidGE_X_of_le Y h) ≫ eqToHom (stupidGE_X_of_le Y (by omega : i ≤ m)).symm else 0
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    by_cases h₁ : i + 1 ≤ m
    · rw [dif_pos h₁, dif_pos (by omega : i + 1 ≤ m + 1), stupidGE_d Y h₁ (by omega),
        stupidGE_d Y (by omega : i ≤ m) (by omega : i ≤ m + 1)]
      simp
    · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

/-- The projection `σ^{≥ i} Y ⟶ Y^i[-i]`. -/
private noncomputable def stupidGEπ (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGE Y i ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) i).obj (Y.X i) :=
  HomologicalComplex.mkHomToSingle (eqToHom (stupidGE_X_of_le Y le_rfl)) fun j hj =>
    (isZero_stupidGE_X_of_lt Y (by simp at hj; omega)).eq_of_src _ _

private lemma stupidGEMap_f_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i + 1 ≤ m) :
    (stupidGEMap Y i).f m =
      eqToHom (stupidGE_X_of_le Y h) ≫ eqToHom (stupidGE_X_of_le Y (by omega : i ≤ m)).symm :=
  dif_pos h

private lemma stupidGEπ_f (Y : CochainComplex C ℤ) (i : ℤ) :
    (stupidGEπ Y i).f i = eqToHom (stupidGE_X_of_le Y le_rfl) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (Y.X i)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

private lemma stupidGEMap_π (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGEMap Y i ≫ stupidGEπ Y i = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  by_cases h : m = i
  · subst h
    exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m h).eq_of_tgt _ _

/-- The short complex `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y ⟶ Y^i[-i]`. -/
private noncomputable def stupidGEShortComplex (Y : CochainComplex C ℤ) (i : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (stupidGEMap Y i) (stupidGEπ Y i) (stupidGEMap_π Y i)

end Trunc

section TruncAbelian

variable {C : Type*} [Category C] [Abelian C]

private lemma stupidGEShortComplex_shortExact (Y : CochainComplex C ℤ) (i m : ℤ) :
    ((stupidGEShortComplex Y i).map (HomologicalComplex.eval _ _ m)).ShortExact := by
  set S := (stupidGEShortComplex Y i).map (HomologicalComplex.eval _ _ m)
  rcases lt_trichotomy m i with h | rfl | h
  · have h₁ : IsZero S.X₁ := isZero_stupidGE_X_of_lt Y (by omega)
    have h₂ : IsZero S.X₂ := isZero_stupidGE_X_of_lt Y h
    have h₃ : IsZero S.X₃ :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m (by omega)
    haveI : Mono S.f := h₁.mono _
    haveI : Epi S.g := h₃.epi _
    exact ⟨ShortComplex.exact_of_isZero_X₂ _ h₂⟩
  · have h₁ : IsZero S.X₁ := isZero_stupidGE_X_of_lt Y (by omega)
    haveI : IsIso S.g := by
      change IsIso ((stupidGEπ Y m).f m)
      rw [stupidGEπ_f]
      infer_instance
    haveI : Mono S.f := h₁.mono _
    exact ⟨(ShortComplex.exact_iff_mono _ (h₁.eq_of_src _ _)).2 inferInstance⟩
  · have h₃ : IsZero S.X₃ :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m (by omega)
    haveI : IsIso S.f := by
      change IsIso ((stupidGEMap Y i).f m)
      rw [stupidGEMap_f_of_le Y (by omega)]
      infer_instance
    haveI : Epi S.g := h₃.epi _
    exact ⟨(ShortComplex.exact_iff_epi _ (h₃.eq_of_tgt _ _)).2 inferInstance⟩

private lemma isIso_stupidGEι (Y : CochainComplex C ℤ) (i : ℤ) (hY : ∀ m, m < i → IsZero (Y.X m)) :
    IsIso (stupidGEι Y i) := by
  haveI : ∀ m, IsIso ((stupidGEι Y i).f m) := fun m => by
    by_cases h : i ≤ m
    · rw [stupidGEι_f_of_le Y h]
      infer_instance
    · exact isIso_of_source_target_iso_zero _ (isZero_stupidGE_X_of_lt Y (by omega)).isoZero
        (hY m (by omega)).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

private lemma isZero_stupidGE (Y : CochainComplex C ℤ) (i : ℤ) (hY : ∀ m, i ≤ m → IsZero (Y.X m)) :
    IsZero (stupidGE Y i) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  by_cases h : i ≤ m
  · exact ((hY m h).of_iso (eqToIso (stupidGE_X_of_le Y h))).eq_of_src _ _
  · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

end TruncAbelian

/-! ### The hypercohomology of a bounded complex -/

section HypercohomologyBound

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `H^j(X, A[-i]) ≅ H^{j-i}(X, A)`. -/
private theorem nonempty_iso_derivedCohomologyOverField_singleFunctor (A : X.Modules) (i j : ℤ) :
    Nonempty (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules i).obj A) j ≅ H f A (j - i)) := by
  let e₁ : ((DerivedCategory.singleFunctor X.Modules 0).obj A)⟦-i⟧ ≅
      (DerivedCategory.singleFunctor X.Modules i).obj A :=
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (-i) i 0 (by omega)).app A
  have e₂ := MMP.Mori.derivedCohomologyOverFieldShiftNegIso f
    ((DerivedCategory.singleFunctor X.Modules 0).obj A) (-i) (-j)
  rw [neg_neg, show -i - -j = j - i by ring] at e₂
  exact ⟨((derivedGlobalSectionsOver f ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).mapIso e₁).symm ≪≫ e₂⟩

/-- The cohomology of a zero object of `D(𝒪_X)` vanishes. -/
private theorem subsingleton_derivedCohomologyOverField_of_isZero {K : DerivedCategory X.Modules}
    (hK : IsZero K) (j : ℤ) : Subsingleton (Stacks.Duality.derivedCohomologyOverField f K j) :=
  ModuleCat.subsingleton_of_isZero
    ((derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).map_isZero hK)

/-- **The hypercohomology of a bounded complex is bounded by that of its terms.** For a complex
`K` of `𝒪_X`-modules concentrated in degrees `0, …, n` whose terms have finite cohomology,
`H^j(X, K)` is finite and `#H^j(X, K) ≤ ∏_{a ≤ n} #H^{j-a}(X, K^a)`: this is the counting form of
the spectral sequence of the stupid filtration. -/
private theorem finite_and_card_le_prod_of_isZero (K : CochainComplex X.Modules ℤ) (n : ℕ)
    (hK : ∀ m : ℤ, (m < 0 ∨ (n : ℤ) < m) → IsZero (K.X m))
    (hfin : ∀ (a : ℕ) (j : ℤ), Finite (H f (K.X a) j)) (j : ℤ) :
    Finite (Stacks.Duality.derivedCohomologyOverField f (DerivedCategory.Q.obj K) j) ∧
      Nat.card (Stacks.Duality.derivedCohomologyOverField f (DerivedCategory.Q.obj K) j) ≤
        ∏ a ∈ Finset.range (n + 1), Nat.card (H f (K.X a) (j - a)) := by
  have key : ∀ (d i : ℕ), i + d = n + 1 → ∀ j : ℤ,
      Finite (Stacks.Duality.derivedCohomologyOverField f
        (DerivedCategory.Q.obj (stupidGE K (i : ℤ))) j) ∧
      Nat.card (Stacks.Duality.derivedCohomologyOverField f
        (DerivedCategory.Q.obj (stupidGE K (i : ℤ))) j) ≤
        ∏ a ∈ Finset.Ico i (n + 1), Nat.card (H f (K.X a) (j - a)) := by
    intro d
    induction d with
    | zero =>
      intro i hi j
      obtain rfl : i = n + 1 := by omega
      haveI := subsingleton_derivedCohomologyOverField_of_isZero f
        (DerivedCategory.Q.map_isZero (isZero_stupidGE K ((n + 1 : ℕ) : ℤ) fun m hm => hK m
          (Or.inr (by push_cast at hm; omega)))) j
      refine ⟨inferInstance, ?_⟩
      rw [Finset.Ico_self, Finset.prod_empty]
      exact Finite.card_le_one_iff_subsingleton.2 inferInstance
    | succ d ih =>
      intro i hi j
      have hS : (stupidGEShortComplex K (i : ℤ)).ShortExact :=
        HomologicalComplex.shortExact_of_degreewise_shortExact _
          (stupidGEShortComplex_shortExact K (i : ℤ))
      obtain ⟨e₃⟩ := nonempty_iso_derivedCohomologyOverField_singleFunctor f (K.X i) i j
      haveI := hfin i (j - i)
      haveI : Finite (Stacks.Duality.derivedCohomologyOverField f
          (DerivedCategory.triangleOfSES hS).obj₃ j) :=
        Finite.of_equiv _ e₃.toLinearEquiv.toEquiv.symm
      have ih' := ih (i + 1) (by omega) j
      push_cast at ih'
      haveI : Finite (Stacks.Duality.derivedCohomologyOverField f
          (DerivedCategory.triangleOfSES hS).obj₁ j) := ih'.1
      obtain ⟨hfin₂, hle⟩ := finite_and_card_le_mul_of_distinguished f _
        (DerivedCategory.triangleOfSES_distinguished hS) j
      refine ⟨hfin₂, hle.trans ?_⟩
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega), mul_comm]
      refine Nat.mul_le_mul ?_ ih'.2
      exact (Nat.card_congr e₃.toLinearEquiv.toEquiv).le
  obtain ⟨h₁, h₂⟩ := key (n + 1) 0 (by omega) j
  haveI : IsIso (stupidGEι K ((0 : ℕ) : ℤ)) :=
    isIso_stupidGEι K _ fun m hm => hK m (Or.inl (by push_cast at hm; omega))
  let e : Stacks.Duality.derivedCohomologyOverField f
      (DerivedCategory.Q.obj (stupidGE K ((0 : ℕ) : ℤ))) j ≅
      Stacks.Duality.derivedCohomologyOverField f (DerivedCategory.Q.obj K) j :=
    (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).mapIso
      (DerivedCategory.Q.mapIso (asIso (stupidGEι K ((0 : ℕ) : ℤ))))
  refine ⟨Finite.of_equiv _ e.toLinearEquiv.toEquiv, ?_⟩
  rw [← Nat.card_congr e.toLinearEquiv.toEquiv, Finset.range_eq_Ico]
  exact h₂

end HypercohomologyBound

/-- The cohomology of a module vanishes in negative degrees. -/
private theorem subsingleton_H_of_neg {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) {j : ℤ} (hj : j < 0) : Subsingleton (H f G j) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) 0 j (-j) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj G) j) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-j) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-j) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) j).some.toEquiv.subsingleton

/-- `#H^m(X, G)` is the cardinality of the Godement cohomology of the underlying abelian sheaf
of `G`. -/
private theorem card_H_eq_card_sheafCohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) (m : ℕ) :
    Nat.card (H f G m) = Nat.card ((MMP.Analytic.sheafCohomology X.toTopCat m).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)) := by
  obtain ⟨e, -⟩ := MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField f G m
  rw [← Nat.card_congr
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f G m).toEquiv]
  exact (Nat.card_congr e.toEquiv).symm

/-! ### Twisting a decomposed complex -/

/-- Isomorphic modules have cohomology groups of the same cardinality. -/
private theorem card_H_congr {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    {G G' : X.Modules} (e : G ≅ G') (j : ℤ) : Nat.card (H f G j) = Nat.card (H f G' j) :=
  Nat.card_congr ((derivedGlobalSectionsOver f ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).mapIso
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso e)).toLinearEquiv.toEquiv

/-- `#H^j(⨁_q E_q[-q]) = ∏_q #H^{j-q}(E_q)`. -/
private theorem card_H_biproduct_singleFunctor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) (E : Fin (n + 1) → X.Modules) (j : ℤ) :
    Nat.card (Stacks.Duality.derivedCohomologyOverField f
      (⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj (E q)) j) =
      ∏ q : Fin (n + 1), Nat.card (H f (E q) (j - q)) := by
  let G := derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j
  let E' := fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj (E q)
  let e : G.obj (⨁ E') ≅ ModuleCat.of k (∀ q, G.obj (E' q)) :=
    G.mapBiproduct E' ≪≫ ModuleCat.biproductIsoPi (fun q => G.obj (E' q))
  refine (Nat.card_congr e.toLinearEquiv.toEquiv).trans ?_
  refine (Nat.card_pi (β := fun q => G.obj (E' q))).trans (Finset.prod_congr rfl fun q _ => ?_)
  obtain ⟨e'⟩ := nonempty_iso_derivedCohomologyOverField_singleFunctor f (E q) q j
  exact Nat.card_congr e'.toLinearEquiv.toEquiv

/-- `- ⊗ M` as an endofunctor of `𝒪_X`-modules. -/
private abbrev twistM {X : Scheme.{u}} (M : X.Modules) : X.Modules ⥤ X.Modules :=
  Stacks.Duality.LocallyFreeTwist.twist X M

private theorem additive_twistM {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    (twistM M).Additive :=
  @Stacks.Duality.LocallyFreeTwist.instAdditiveModTwist X M hM

private theorem preservesFiniteLimits_twistM {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    PreservesFiniteLimits (twistM M) :=
  @Stacks.Duality.LocallyFreeTwist.instPreservesFiniteLimitsModTwist X M hM

private theorem preservesFiniteColimits_twistM {X : Scheme.{u}} (M : X.Modules) :
    PreservesFiniteColimits (twistM M) :=
  Stacks.Duality.LocallyFreeTwist.instPreservesFiniteColimitsModTwist (X := X) M

attribute [local instance] additive_twistM preservesFiniteLimits_twistM
  preservesFiniteColimits_twistM

/-- **Cohomology of a twisted decomposed complex.** If `Q(B) ≅ ⨁_{q ≤ n} E_q[-q]` in `D(𝒪_X)`
and `M` is finite locally free, then `#H^j(X, B ⊗ M) = ∏_q #H^{j-q}(X, E_q ⊗ M)`. -/
private theorem card_derivedCohomologyOverField_twist_eq_prod {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) (E : Fin (n + 1) → X.Modules)
    (B : CochainComplex X.Modules ℤ)
    (Φ : (⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj (E q)) ≅
      DerivedCategory.Q.obj B)
    (M : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (j : ℤ) :
    Nat.card (Stacks.Duality.derivedCohomologyOverField f (DerivedCategory.Q.obj
      (((twistM M).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) j) =
      ∏ q : Fin (n + 1), Nat.card (H f ((twistM M).obj (E q)) (j - q)) := by
  let tw := twistM M
  let eL : tw.mapDerivedCategory.obj
        (⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj (E q)) ≅
      ⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj
        (tw.obj (E q)) :=
    tw.mapDerivedCategory.mapBiproduct _ ≪≫
      biproduct.mapIso fun q => (tw.mapDerivedCategorySingleFunctor (q : ℤ)).app _
  let e : (⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj
        (tw.obj (E q))) ≅
      DerivedCategory.Q.obj ((tw.mapHomologicalComplex (ComplexShape.up ℤ)).obj B) :=
    eL.symm ≪≫ tw.mapDerivedCategory.mapIso Φ ≪≫ tw.mapDerivedCategoryFactors.app B
  let e' : Stacks.Duality.derivedCohomologyOverField f
      (⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor X.Modules (q : ℤ)).obj
        (tw.obj (E q))) j ≅
      Stacks.Duality.derivedCohomologyOverField f
        (DerivedCategory.Q.obj ((tw.mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) j :=
    (derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).mapIso e
  exact (Nat.card_congr e'.toLinearEquiv.toEquiv).symm.trans
    (card_H_biproduct_singleFunctor f n _ j)

/-- **`Ω^m_{X/S} = 0` for `m > d`** when `X` is smooth of relative dimension `d` over `S`: the
exterior powers of a finite locally free module of rank `d` vanish above `d`. -/
private theorem isZero_relativeDifferentialForms_of_lt {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] (m : ℤ) (hm : (d : ℤ) < m) :
    IsZero (Scheme.Hom.relativeDifferentialForms f m) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ m by omega)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)
      (Scheme.Hom.relativeDifferentials f) d :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f d
  refine (IsZero.iff_id_eq_zero _).2 (_root_.SheafOfModules.hom_ext ?_)
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt
    (_root_.SheafOfModules.algebras _ (Scheme.Hom.relativeDifferentials f)) d m (by omega) U z

/-- `Ω^a_{X/S}` is finite locally free when `f` is smooth of relative dimension `n`. -/
private theorem isFiniteLocallyFree_exteriorPower {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n f] (a : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a) :=
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f n
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (hM := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (Scheme.Hom.relativeDifferentials f) n a) _ (n.choose a)

/-- `Ω^a ⊗ M` is finite locally free for `M` invertible and `f` smooth of relative dimension
`n`. -/
private theorem isFiniteLocallyFree_formsTensor {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n f] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (a : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (formsTensor f a M) :=
  Stacks.Chow.isFiniteLocallyFree_tensor (isFiniteLocallyFree_exteriorPower f n a)
    (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1)

/-- The dual of an invertible module is invertible. -/
private theorem isInvertible_dualSheaf {X : Scheme.{u}} (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) :=
  Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf _ N

/-! ### Picard classes -/

section Picard

variable {X : Scheme.{u}}

/-- The Picard class of an invertible `𝒪_X`-module. -/
private abbrev pic (L : X.Modules) (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.presheaf X.ringCatSheaf.2 L h

private theorem pic_eq_iff (L L' : X.Modules)
    (h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (h' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L') :
    pic L h = pic L' h' ↔ Nonempty (L ≅ L') :=
  Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatSheaf.2 L L' h h'

/-- `[L^∨] = -[L]`. -/
private theorem pic_dualSheaf (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    pic (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) (isInvertible_dualSheaf L) =
      -pic L h := by
  haveI := isInvertible_dualSheaf L
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).mp h
  let e' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) ≅
      _root_.SheafOfModules.unit _ :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).mapIso
      (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
        X.ringCatSheaf.2 L N e)).symm ≪≫ e
  have hLD : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj L).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.2 _ _
  have hsum : pic L h + pic _ (isInvertible_dualSheaf L) = pic _ hLD :=
    Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf X.ringCatSheaf.2 L
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) h (isInvertible_dualSheaf L) hLD
  have hzero : pic _ hLD = 0 :=
    ((pic_eq_iff _ _ hLD _).2 ⟨e'⟩).trans
      (Stacks.SheafOfModules.picardClass_zero X.presheaf X.ringCatSheaf.2)
  exact eq_neg_of_add_eq_zero_right (hsum.trans hzero)

/-- `[L^{⊗ d}] = d [L]`. -/
private theorem pic_tensorPowModule (L : X.Modules)
    [h : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (d : ℕ) :
    pic (Stacks.Ample.tensorPowModule X L d)
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L d) = (d : ℤ) • pic L h := by
  rw [← Stacks.Picard.classOf_tensorPower X.presheaf X.ringCatSheaf.2 L d]
  exact (pic_eq_iff _ _ _ _).2
    ⟨(Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow X.presheaf X.ringCatSheaf.2 L d).symm⟩

end Picard

/-! ### Serre duality and Serre vanishing -/

section Serre

/-- If `G ≅ G'` and `H^j(X, G')` vanishes, then so does `H^j(X, G)`. -/
private theorem subsingleton_H_congr {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) {G G' : X.Modules} (e : G ≅ G') (j : ℤ) [h : Subsingleton (H f G' j)] :
    Subsingleton (H f G j) :=
  @Equiv.subsingleton _ _ ((derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} k) j).mapIso ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      e)).toLinearEquiv.toEquiv h

/-- Vanishing of `Hgroup`, the abelian sheaf cohomology of `Stacks.Ample`, gives vanishing of the
cohomology over the base field. -/
private theorem subsingleton_H_of_isZero_Hgroup {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) (i : ℕ) (h : IsZero (Hgroup X.ringCatSheaf ⊤ i G)) :
    Subsingleton (H f G i) := by
  haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ i G) := AddCommGrpCat.subsingleton_of_isZero h
  haveI : Subsingleton (cohomologyOverField k f G i) :=
    (cohomologyOverFieldAddEquivHgroup k f G i).toEquiv.subsingleton
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f G
    i).toEquiv.symm.subsingleton

/-- **Serre vanishing**, in the spelling of this file: for `L` ample and `G` coherent on a proper
scheme over a field, `H^i(G ⊗ L^{⊗ d}) = 0` for all `i > 0` and all large `d`. -/
private theorem exists_subsingleton_H_tensor_tensorPowModule {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (G : X.Modules)
    [SheafOfModules.IsCoherent G] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ i : ℤ, 0 < i →
      Subsingleton (H f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.toRingedSpace.sheaf).obj G).obj (Stacks.Ample.tensorPowModule X L d)) i) := by
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f G L hL
  refine ⟨d₀, fun d hd i hi => ?_⟩
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact subsingleton_H_of_isZero_Hgroup f _ m (hd₀ d m hd (by omega))

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-- `(A ⊗ B)^∨ ≅ B^∨ ⊗ A^∨` for finite locally free `A` and `B`: both are right duals of
`A ⊗ B`. -/
private def dualSheafTensorIso {X : Scheme.{u}} (A B : X.Modules)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} B) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf B)).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A) :=
  @rightDualIso _ _ _ _ _ _ (@Stacks.Duality.LocallyFreeTwist.pairing X (A ⊗ B)
      (Stacks.Chow.isFiniteLocallyFree_tensor hA hB))
    (@ExactPairing.tensor _ _ _ (A : Stacks.Duality.LocallyFreeTwist.Mod X)
      (B : Stacks.Duality.LocallyFreeTwist.Mod X) (Stacks.Duality.LocallyFreeTwist.dual A)
      (Stacks.Duality.LocallyFreeTwist.dual B)
      (@Stacks.Duality.LocallyFreeTwist.pairing X A hA)
      (@Stacks.Duality.LocallyFreeTwist.pairing X B hB))

/-- **Serre duality, in the form used here.** On `X` proper and smooth of relative dimension `n`
over a field, for `M` invertible, `H^j(Ω^a ⊗ M) = 0` as soon as
`H^{n-j}((Ω^n ⊗ (Ω^a)^∨) ⊗ M^∨) = 0`. -/
private theorem subsingleton_H_formsTensor_of_subsingleton_dual {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (a : ℕ) (j : ℤ)
    (h : Subsingleton (H f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.toRingedSpace.sheaf).obj (formsTensor f n
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)))).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)) (n - j))) :
    Subsingleton (H f (formsTensor f a M) j) := by
  obtain ⟨L⟩ := MMP.Mori.nonempty_dual_linearEquiv_exteriorPower_tensor_dual f n
    (formsTensor f a M) (hF := isFiniteLocallyFree_formsTensor f n M a) j
  let Ωn := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n
  let A := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf
  let e : (T.obj Ωn).obj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf ((T.obj A).obj M)) ≅
      (T.obj ((T.obj Ωn).obj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A))).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M) :=
    (T.obj Ωn).mapIso (dualSheafTensorIso A M (isFiniteLocallyFree_exteriorPower f n a)
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.toRingedSpace.sheaf).app _).app _) ≪≫
      (α_ (Ωn : Stacks.Duality.LocallyFreeTwist.Mod X)
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A)
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M)).symm
  have h' := subsingleton_H_congr f e (n - j)
  haveI : Subsingleton (Module.Dual k (H f (formsTensor f a M) j)) := @Equiv.subsingleton _ _
    L.toEquiv h'
  exact (Module.subsingleton_dual_iff k).1 this

end Serre

/-- **A differential operator of order one commutes with `p`-th powers in characteristic `p`.**
If every commutator `s ↦ D(g s) - g D s` is `R`-linear and `p = 0` in `R`, then
`D(g^p s) = g^p D s`: the commutator `c_g` is a derivation in `g`, so `c_{g^p} = p g^{p-1} c_g`. -/
private theorem pow_smul_of_commutator {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (D : M →+ N)
    (hD : ∀ (g r : R) (s : M), D (g • r • s) - g • D (r • s) = r • (D (g • s) - g • D s))
    (p : ℕ) (hp : (p : R) = 0) (g : R) (s : M) : D (g ^ p • s) = g ^ p • D s := by
  have hpow : ∀ m : ℕ, D (g ^ (m + 1) • s) - g ^ (m + 1) • D s =
      ((m + 1 : ℕ) : R) • g ^ m • (D (g • s) - g • D s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : D (g ^ (m + 1 + 1) • s) - g ^ (m + 1 + 1) • D s =
          (D (g • g ^ (m + 1) • s) - g • D (g ^ (m + 1) • s)) +
            g • (D (g ^ (m + 1) • s) - g ^ (m + 1) • D s) := by
        rw [pow_succ' g (m + 1), mul_smul, mul_smul, smul_sub]
        abel
      rw [h1, hD, ih]
      simp only [smul_smul]
      rw [← add_smul]
      congr 1
      push_cast
      ring
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simpa [hp, sub_eq_zero] using hpow m

/-! ### Characteristic `p` -/

section CharP

variable (p : ℕ) [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
  {V : Scheme.{u}} (f : V ⟶ Spec (.of F))

include f in
/-- A scheme over a field of characteristic `p` is in characteristic `p`. -/
private theorem isInCharacteristic_of_charP : Stacks.Frobenius.IsInCharacteristic V p := by
  have h : ((p : ℕ) : Γ(Spec (.of F), ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (.of F)).inv.hom, CharP.cast_eq_zero, map_zero]
  change ((p : ℕ) : Γ(V, ⊤)) = 0
  rw [← map_natCast f.appTop.hom, h, map_zero]

variable {p} (hV : Stacks.Frobenius.IsInCharacteristic V p)

/-- `F^*M`, the pullback of a module along the absolute Frobenius. -/
private abbrev frobeniusPullback (M : V.Modules) : V.Modules :=
  (Scheme.Modules.pullback (Stacks.Frobenius.absoluteFrobenius V p hV)).obj M

/-- The Frobenius pullback of an invertible module is invertible. -/
private theorem isInvertible_frobeniusPullback (M : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] :
    SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 (frobeniusPullback hV M) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ M

/-- The iterated Frobenius pullbacks of an invertible module are invertible. -/
private theorem isInvertible_frobeniusPullback_iterate (M : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] (e : ℕ) :
    SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 ((frobeniusPullback hV)^[e] M) := by
  induction e with
  | zero => assumption
  | succ e ih =>
    rw [Function.iterate_succ_apply']
    haveI := ih
    exact isInvertible_frobeniusPullback hV _

/-- On a proper scheme over a finite field the cohomology of `Ω^a ⊗ M`, for `M` invertible, is
finite. -/
private theorem finite_H_formsTensor [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (M : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] (a : ℕ) (j : ℤ) :
    Finite (H f (formsTensor f a M) j) := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := isFiniteLocallyFree_formsTensor f n M a
  haveI := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree V
    (formsTensor f a M)
  haveI := MMP.Mori.finiteDimensional_derivedCohomologyOverField_single_of_isCoherent f
    (formsTensor f a M) j
  exact Module.finite_of_finite F

/-- `Ω^a = 0` for `a > n` on a scheme smooth of relative dimension `n`, so `H^j(Ω^a ⊗ M) = 0`. -/
private theorem subsingleton_H_formsTensor_of_lt (n : ℕ) [SmoothOfRelativeDimension n f]
    (M : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] (a : ℕ)
    (ha : n < a) (j : ℤ) : Subsingleton (H f (formsTensor f a M) j) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
  have hz : IsZero (formsTensor f a M) :=
    (twistM M).map_isZero (isZero_relativeDifferentialForms_of_lt f n a (by omega))
  exact subsingleton_derivedCohomologyOverField_of_isZero f
    ((DerivedCategory.singleFunctor V.Modules 0).map_isZero hz) j

/-- `F_*Ω^q`, the Frobenius pushforward of the sheaf of differential `q`-forms. -/
private abbrev frobeniusForms (q : ℕ) : V.Modules :=
  (Scheme.Modules.pushforward (Stacks.Frobenius.absoluteFrobenius V p hV)).obj
    (Scheme.Hom.relativeDifferentialForms f (q : ℤ))

include hV in
/-- The de Rham differential commutes with `p`-th powers of functions in characteristic `p`. -/
private theorem deRhamGlobalOp_pow_smul (q : ℕ) (U : V.Opensᵒᵖ)
    (g : V.toRingedSpace.sheaf.obj.obj U)
    (s : ((Scheme.Hom.deRhamAlgebras f).exteriorPower q).val.obj U) :
    AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q U
        (g ^ p • s) =
      g ^ p • AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q U s :=
  pow_smul_of_commutator _
    (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp_commutator_smul _ q U) p
    (Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hV U.unop) g s

/-- The de Rham differential `F_*Ω^q ⟶ F_*Ω^{q+1}` on the underlying presheaves of abelian
groups. -/
private def frobeniusDeRhamDPresheaf (q : ℕ) :
    (frobeniusForms f hV q).val.presheaf ⟶ (frobeniusForms f hV (q + 1)).val.presheaf := by
  let φ₀ := (PresheafOfModules.toPresheaf _).map
    (AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom (Scheme.Hom.deRhamAlgebras f) q).val
  exact φ₀

/-- The de Rham differential `F_*Ω^q ⟶ F_*Ω^{q+1}`: it is `𝒪_V`-linear for the Frobenius-twisted
module structures because `d(a^p ω) = a^p dω` in characteristic `p`. -/
private def frobeniusDeRhamD (q : ℕ) : frobeniusForms f hV q ⟶ frobeniusForms f hV (q + 1) :=
  _root_.SheafOfModules.Hom.mk (PresheafOfModules.homMk (frobeniusDeRhamDPresheaf f hV q)
    fun W r s => by
      change @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
          (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W
            (@id Γ(V, W.unop) ((Stacks.Frobenius.absoluteFrobenius V p hV).app W.unop r) •
              @id Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W.unop) s)) =
        @id Γ(V, W.unop) ((Stacks.Frobenius.absoluteFrobenius V p hV).app W.unop r) •
          @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W s)
      have h := Stacks.Frobenius.absoluteFrobenius_app_apply V p hV W.unop r
      exact (congrArg (fun x : Γ(V, W.unop) =>
        @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W
              (x • @id Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W.unop) s)) =
          x • @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W s))
        h).mpr (deRhamGlobalOp_pow_smul f hV q W r s))

private theorem frobeniusDeRhamD_app (q : ℕ) (W : V.Opens)
    (s : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ),
      Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)) :
    (frobeniusDeRhamD f hV q).app W s =
      ((Scheme.Hom.deRhamComplex f).d q (q + 1)).val.app (Opposite.op W) s := by
  rw [Scheme.Hom.deRhamComplex_d]
  rfl

private theorem frobeniusDeRhamD_comp (q : ℕ) :
    frobeniusDeRhamD f hV q ≫ frobeniusDeRhamD f hV (q + 1) = 0 := by
  ext W s
  exact congrArg (fun φ => φ.val.app (Opposite.op W) s)
    ((AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)).squared q)

/-- The Frobenius pushforward `F_*Ω^•_V` of the de Rham complex, as a complex of `𝒪_V`-modules
indexed by `ℤ`. -/
private abbrev frobeniusDeRhamComplex : CochainComplex V.Modules ℤ :=
  (CochainComplex.of (frobeniusForms f hV) (frobeniusDeRhamD f hV)
    (frobeniusDeRhamD_comp f hV)).extend ComplexShape.embeddingUpNat

/-- Restricting twice is restricting once. -/
private theorem presheaf_map_map_apply {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens}
    (h₁ : B ≤ A) (h₂ : C ≤ B) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting to the same open is the identity. -/
private theorem presheaf_map_self_apply {X : Scheme.{u}} (M : X.Modules) {A : X.Opens}
    (h : A ≤ A) (x : Γ(M, A)) : M.presheaf.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A smooth morphism of relative dimension `n`, read through the empty simple normal crossing
divisor: the conditions of
`MMP.DeRham.nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift` at
`ι = Empty`. -/
private theorem smoothOfRelativeDimension_iSup_empty {Y T : Scheme.{u}} (h : Y ⟶ T) (n : ℕ)
    [SmoothOfRelativeDimension n h] (K : Empty → Y.IdealSheafData) (Tf : Finset Empty) :
    SmoothOfRelativeDimension (n - Tf.card) ((⨆ j ∈ Tf, K j).subschemeι ≫ h) ∧
      (n < Tf.card → IsEmpty (⨆ j ∈ Tf, K j).subscheme) := by
  obtain rfl : Tf = ∅ := Subsingleton.elim _ _
  have hbot : (⨆ j ∈ (∅ : Finset Empty), K j) = ⊥ := iSup_of_empty _
  rw [hbot]
  refine ⟨?_, fun h => absurd h (Nat.not_lt_zero _)⟩
  have := (inferInstance :
    SmoothOfRelativeDimension (0 + n) ((⊥ : Y.IdealSheafData).subschemeι ≫ h))
  rw [zero_add] at this
  simpa using this

/-- **The Deligne--Illusie decomposition** `⨁_{q ≤ n} Ω^q[-q] ≅ F_*Ω^•` in `D(𝒪_V)`. -/
private theorem nonempty_iso_frobeniusDeRhamComplex (n : ℕ) (hpn : n < p) [IsProper f]
    [SmoothOfRelativeDimension n f]
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F)))
    [SmoothOfRelativeDimension n g]
    (π : TruncatedWittVector p 2 F →+* F) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π))) :
    Nonempty ((⨁ fun q : Fin (n + 1) ↦ (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj
        (Scheme.Hom.relativeDifferentialForms f ((q : ℕ) : ℤ))) ≅
      DerivedCategory.Q.obj (frobeniusDeRhamComplex f hV)) := by
  let J : Empty → V.IdealSheafData := fun j => j.elim
  let I : Empty → 𝒱.IdealSheafData := fun j => j.elim
  set U : V.Opens := ((⨅ j, J j).support).compl with hUdef
  have hUtop : U = ⊤ := by
    rw [hUdef, iInf_of_empty]
    ext x
    simp [Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.compl]
  have hle : ∀ W : V.Opens, W ≤ W ⊓ U := fun W => by rw [hUtop, inf_top_eq]
  let K : ℕ → V.Modules := fun q => Scheme.Hom.relativeDifferentialForms f (q : ℤ)
  let e : ∀ (q : ℕ) (W : V.Opens), Γ(K q, W) →+
      Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W ⊓ U) :=
    fun q W => ((K q).presheaf.map (homOfLE inf_le_left).op).hom
  have he_inj : ∀ (q : ℕ) W, Function.Injective (e q W) := by
    intro q W x y hxy
    have h := congrArg ((K q).presheaf.map (homOfLE (hle W)).op).hom hxy
    simp only [e] at h
    rwa [presheaf_map_map_apply, presheaf_map_map_apply, presheaf_map_self_apply,
      presheaf_map_self_apply] at h
  have he_smul : ∀ (q : ℕ) W (a : Γ(V, W)) (s : Γ(K q, W)),
      e q W (a • s) = V.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op a • e q W s :=
    fun q W a s => Scheme.Modules.map_smul (K q) (homOfLE inf_le_left) a s
  have he_res : ∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (s : Γ(K q, W₂)),
      e q W₁ ((K q).presheaf.map (homOfLE h).op s) =
        (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
          (homOfLE (inf_le_inf_right _ h)).op (e q W₂ s) := by
    intro q W₁ W₂ h s
    simp only [e]
    rw [presheaf_map_map_apply, presheaf_map_map_apply]
  have he_range : ∀ (q : ℕ) (W : V.Opens)
      (ω : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W ⊓ U)),
      ω ∈ Set.range (e q W) ↔
        ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : Empty → Γ(V, W')),
          (∀ j, c j ∈ (J j).ideal W') →
          (∃ η : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W'),
            (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op ω) ∧
          (∃ η : Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W'),
            (Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op
                    (((f.deRhamComplex).d q (q + 1)).val.app (Opposite.op (W ⊓ U)) ω)) := by
    intro q W ω
    refine iff_of_true ⟨(K q).presheaf.map (homOfLE (hle W)).op ω, ?_⟩ fun W' hW' c _ => ⟨?_, ?_⟩
    · simp only [e]
      rw [presheaf_map_map_apply, presheaf_map_self_apply]
    · refine ⟨(Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
        (homOfLE ((hle _).trans (inf_le_inf_right U hW'))).op ω, ?_⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact presheaf_map_map_apply _ _ _ ω
    · refine ⟨(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE ((hle _).trans (inf_le_inf_right U hW'))).op
          (((f.deRhamComplex).d q (q + 1)).val.app (Opposite.op (W ⊓ U)) ω), ?_⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact presheaf_map_map_apply _ _ _ _
  have he_d : ∀ (q : ℕ) (W : V.Opens) (s : Γ(K q, Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)),
      e (q + 1) (Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)
          ((frobeniusDeRhamD f hV q).app W s) =
        ((f.deRhamComplex).d q (q + 1)).val.app
          (Opposite.op (Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W ⊓ U)) (e q _ s) := by
    intro q W s
    rw [frobeniusDeRhamD_app]
    exact (PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamComplex f).d q (q + 1)).val
      (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s).symm
  exact (MMP.DeRham.nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift
    p n hpn f hV J (smoothOfRelativeDimension_iSup_empty f n J) g I π hπ i hi (fun j => j.elim)
    (smoothOfRelativeDimension_iSup_empty g n I) U hUdef K e he_inj he_smul he_res he_range
    (frobeniusDeRhamD f hV) (frobeniusDeRhamD_comp f hV) he_d).1

/-- `#H^j(F_*G) = #H^j(G)`: the Frobenius pushforward has the same underlying abelian sheaf. -/
private theorem card_H_pushforward_frobenius (G : V.Modules) (j : ℤ) :
    Nat.card (H f ((Scheme.Modules.pushforward
      (Stacks.Frobenius.absoluteFrobenius V p hV)).obj G) j) =
      Nat.card (H f G j) := by
  rcases lt_or_ge j 0 with hj | hj
  · haveI := subsingleton_H_of_neg f G hj
    haveI := subsingleton_H_of_neg f
      ((Scheme.Modules.pushforward (Stacks.Frobenius.absoluteFrobenius V p hV)).obj G) hj
    rw [Nat.card_unique, Nat.card_unique]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [card_H_eq_card_sheafCohomology, card_H_eq_card_sheafCohomology]
    rfl

/-- **The projection formula** `F_*Ω^a ⊗ M ≅ F_*(Ω^a ⊗ F^*M)` for `M` invertible. -/
private theorem nonempty_iso_frobeniusForms_tensor (M : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] (a : ℕ) :
    Nonempty ((twistM M).obj (frobeniusForms f hV a) ≅
      (Scheme.Modules.pushforward (Stacks.Frobenius.absoluteFrobenius V p hV)).obj
        (formsTensor f a (frobeniusPullback hV M))) := by
  haveI : Stacks.SheafOfModules.IsInvertible V.toRingedSpace.sheaf.obj
      (Stacks.RingedSpace.structureRingSheaf V.toRingedSpace).property M :=
    ‹SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M›
  exact ⟨Stacks.ProjectionFormula.projectionFormulaIso
    (Stacks.Frobenius.absoluteFrobenius V p hV).toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) M⟩

/-- **The Deligne--Illusie inequality.** Over a finite field of characteristic `p > n`, for `V`
proper and smooth of relative dimension `n` with a `W₂`-lift and `M` invertible,
`∏_{a ≤ n} #H^{j-a}(Ω^a ⊗ M) ≤ ∏_{a ≤ n} #H^{j-a}(Ω^a ⊗ F^*M)` for every `j`. -/
private theorem prod_card_le_prod_card_frobeniusPullback (n : ℕ) (hpn : n < p) [IsProper f]
    [SmoothOfRelativeDimension n f]
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F)))
    [SmoothOfRelativeDimension n g]
    (π : TruncatedWittVector p 2 F →+* F) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π)))
    (M : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M] (j : ℤ) :
    ∏ a ∈ Finset.range (n + 1), Nat.card (H f (formsTensor f a M) (j - a)) ≤
      ∏ a ∈ Finset.range (n + 1),
        Nat.card (H f (formsTensor f a (frobeniusPullback hV M)) (j - a)) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI := isInvertible_frobeniusPullback hV M
  obtain ⟨Φ⟩ := nonempty_iso_frobeniusDeRhamComplex f hV n hpn g π hπ i hi
  let tw := twistM M
  let B' : CochainComplex V.Modules ℤ :=
    (tw.mapHomologicalComplex (ComplexShape.up ℤ)).obj (frobeniusDeRhamComplex f hV)
  have hX : ∀ a : ℕ, (frobeniusDeRhamComplex f hV).X (a : ℤ) ≅ frobeniusForms f hV a :=
    fun a => HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f a)
  -- the terms of `B'`
  have hterm : ∀ (a : ℕ) (j' : ℤ), Nat.card (H f (B'.X a) j') =
      Nat.card (H f (formsTensor f a (frobeniusPullback hV M)) j') := by
    intro a j'
    obtain ⟨eP⟩ := nonempty_iso_frobeniusForms_tensor f hV M a
    rw [show B'.X a = tw.obj ((frobeniusDeRhamComplex f hV).X a) from rfl,
      card_H_congr f (tw.mapIso (hX a) ≪≫ eP), card_H_pushforward_frobenius f hV]
  have hfin : ∀ (a : ℕ) (j' : ℤ), Finite (H f (B'.X a) j') := fun a j' => by
    haveI := finite_H_formsTensor f n (frobeniusPullback hV M) a j'
    exact Nat.finite_of_card_ne_zero (by rw [hterm]; exact Nat.card_pos.ne')
  have hB' : ∀ m : ℤ, (m < 0 ∨ (n : ℤ) < m) → IsZero (B'.X m) := by
    intro m hm
    rw [show B'.X m = tw.obj ((frobeniusDeRhamComplex f hV).X m) from rfl]
    refine tw.map_isZero ?_
    rcases hm with hm | hm
    · exact HomologicalComplex.isZero_extend_X _ _ _ fun i' h' => by
        rw [ComplexShape.embeddingUpNat_f] at h'; omega
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, m = (a : ℤ) := ⟨m.toNat, by omega⟩
      exact IsZero.of_iso ((Scheme.Modules.pushforward _).map_isZero
        (isZero_relativeDifferentialForms_of_lt f n (a : ℤ) hm)) (hX a)
  obtain ⟨-, hle⟩ := finite_and_card_le_prod_of_isZero f B' n hB' hfin j
  have h₁ := card_derivedCohomologyOverField_twist_eq_prod f n
    (fun q => Scheme.Hom.relativeDifferentialForms f ((q : ℕ) : ℤ)) _ Φ M j
  rw [← Fin.prod_univ_eq_prod_range (fun a => Nat.card (H f (formsTensor f a M) (j - a)))]
  exact (h₁.symm.trans_le hle).trans_eq (Finset.prod_congr rfl fun a _ => hterm a (j - a))

/-- `[F^*L] = p [L]`: pulling back along the absolute Frobenius is multiplication by `p` on the
Picard group. -/
private theorem pic_frobeniusPullback (L : V.Modules)
    [h : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L] :
    pic (frobeniusPullback hV L) (isInvertible_frobeniusPullback hV L) = (p : ℤ) • pic L h :=
  (Stacks.Picard.pullbackClass_classOf _ L h).symm.trans
    (Stacks.Picard.schemePullbackClass_absoluteFrobenius V p hV (pic L h))

/-- `[F^{e*}L] = p^e [L]`. -/
private theorem pic_frobeniusPullback_iterate (L : V.Modules)
    [h : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L] (e : ℕ) :
    pic ((frobeniusPullback hV)^[e] L) (isInvertible_frobeniusPullback_iterate hV L e) =
      ((p ^ e : ℕ) : ℤ) • pic L h := by
  induction e with
  | zero => exact (one_smul ℤ _).symm
  | succ e ih =>
    haveI := isInvertible_frobeniusPullback_iterate hV L e
    have h₁ : pic ((frobeniusPullback hV)^[e + 1] L)
        (isInvertible_frobeniusPullback_iterate hV L (e + 1)) =
        pic (frobeniusPullback hV ((frobeniusPullback hV)^[e] L))
          (isInvertible_frobeniusPullback hV _) := by
      congr 1
      exact Function.iterate_succ_apply' _ _ _
    rw [h₁, pic_frobeniusPullback, ih, smul_smul]
    congr 1
    push_cast
    ring

/-- **The Frobenius twists of `N^{-1}`.** `(F^{e*}N^{-1})^∨ ≅ N^{⊗ p^e}`: pulling back along the
absolute Frobenius is multiplication by `p` on the Picard group. -/
private theorem nonempty_iso_dualSheaf_frobeniusPullback_iterate (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] (e : ℕ) :
    Nonempty (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((frobeniusPullback hV)^[e] (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) ≅
      Stacks.Ample.tensorPowModule V N ((p ^ e : ℕ) : ℤ)) := by
  haveI := isInvertible_dualSheaf N
  haveI := isInvertible_frobeniusPullback_iterate hV
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) e
  refine (pic_eq_iff _ _ (isInvertible_dualSheaf _)
    (Stacks.Ample.isInvertibleModule_tensorPowModule V N _)).1 ?_
  rw [pic_dualSheaf, pic_frobeniusPullback_iterate hV _ e, pic_dualSheaf, pic_tensorPowModule,
    smul_neg, neg_neg]

/-- **Serre duality and Serre vanishing for the Frobenius twists.** For `N` ample and invertible,
`H^j(Ω^a ⊗ F^{e*}N^{-1}) = 0` whenever `a + j < n`, for all large `e`. -/
private theorem exists_subsingleton_H_formsTensor_frobeniusPullback_iterate (n : ℕ) [IsProper f]
    [SmoothOfRelativeDimension n f] (N : V.Modules)
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N] (hN : Stacks.Ample.IsAmple V N) :
    ∃ e : ℕ, ∀ (a : ℕ) (j : ℤ), (a : ℤ) + j < n →
      Subsingleton (H f (formsTensor f a ((frobeniusPullback hV)^[e]
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N))) j) := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := isInvertible_dualSheaf N
  -- the coherent sheaves `Ω^n ⊗ (Ω^a)^∨` and their Serre bounds
  have hG : ∀ a : ℕ, SheafOfModules.IsCoherent (formsTensor f n
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a))) := fun a =>
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree V _ _
      (Stacks.Chow.isFiniteLocallyFree_tensor (isFiniteLocallyFree_exteriorPower f n n)
        (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf _
          (isFiniteLocallyFree_exteriorPower f n a)))
  choose d₀ hd₀ using fun a : ℕ => haveI := hG a
    exists_subsingleton_H_tensor_tensorPowModule f (formsTensor f n
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a))) N hN
  let D := (Finset.range (n + 1)).sup d₀
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  refine ⟨D, fun a j haj => ?_⟩
  haveI := isInvertible_frobeniusPullback_iterate hV
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N) D
  rcases lt_or_ge n a with ha | ha
  · exact subsingleton_H_formsTensor_of_lt f n _ a ha j
  refine subsingleton_H_formsTensor_of_subsingleton_dual f n _ a j ?_
  obtain ⟨eP⟩ := nonempty_iso_dualSheaf_frobeniusPullback_iterate hV N D
  have hle : d₀ a ≤ p ^ D :=
    (Finset.le_sup (f := d₀) (Finset.mem_range.2 (by omega))).trans (Nat.lt_pow_self hp).le
  haveI := hd₀ a (p ^ D) hle (n - j) (by omega)
  exact subsingleton_H_congr f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    V.toRingedSpace.sheaf).obj _).mapIso eP) (n - j)

end CharP

/-- **Akizuki--Nakano vanishing over a finite field with a `W₂`-lift.** -/
private theorem subsingleton_H_formsTensor_dualSheaf_of_finite (p : ℕ) [Fact p.Prime]
    {F : Type u} [Field F] [Finite F] [CharP F p] (n : ℕ) (hpn : n < p)
    {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) [IsProper f] [SmoothOfRelativeDimension n f]
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F)))
    [SmoothOfRelativeDimension n g]
    (π : TruncatedWittVector p 2 F →+* F) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π)))
    (N : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N]
    (hN : Stacks.Ample.IsAmple V N) (a : ℕ) (q : ℤ) (haq : (a : ℤ) + q < n) :
    Subsingleton
      (H f (formsTensor f a (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) q) := by
  have hV := isInCharacteristic_of_charP p f
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI := isInvertible_dualSheaf N
  rcases lt_or_ge n a with ha | ha
  · exact subsingleton_H_formsTensor_of_lt f n _ a ha q
  obtain ⟨e, he⟩ := exists_subsingleton_H_formsTensor_frobeniusPullback_iterate f hV n N hN
  set M₀ := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N
  set j : ℤ := a + q
  -- the inequality, iterated
  have hiter : ∀ e' : ℕ, ∏ b ∈ Finset.range (n + 1), Nat.card (H f (formsTensor f b M₀) (j - b)) ≤
      ∏ b ∈ Finset.range (n + 1),
        Nat.card (H f (formsTensor f b ((frobeniusPullback hV)^[e'] M₀)) (j - b)) := by
    intro e'
    induction e' with
    | zero => exact le_rfl
    | succ e' ih =>
      haveI := isInvertible_frobeniusPullback_iterate hV M₀ e'
      refine ih.trans ?_
      rw [Function.iterate_succ_apply']
      exact prod_card_le_prod_card_frobeniusPullback f hV n hpn g π hπ i hi _ j
  -- the right side is `1`
  have hone : ∏ b ∈ Finset.range (n + 1),
      Nat.card (H f (formsTensor f b ((frobeniusPullback hV)^[e] M₀)) (j - b)) = 1 := by
    refine Finset.prod_eq_one fun b hb => ?_
    haveI := he b (j - b) (by omega)
    haveI := isInvertible_frobeniusPullback_iterate hV M₀ e
    haveI := finite_H_formsTensor f n ((frobeniusPullback hV)^[e] M₀) b (j - b)
    exact Nat.card_unique
  -- every factor on the left is at least `1`
  have hpos : ∀ b, 1 ≤ Nat.card (H f (formsTensor f b M₀) (j - b)) := fun b => by
    haveI := finite_H_formsTensor f n M₀ b (j - b)
    exact Nat.card_pos
  have hle : Nat.card (H f (formsTensor f a M₀) (j - a)) ≤ 1 := by
    have h := (hiter e).trans hone.le
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 (by omega : a < n + 1))] at h
    exact le_of_mul_le_of_one_le_left h (Finset.one_le_prod' fun b _ => hpos b)
  haveI := finite_H_formsTensor f n M₀ a (j - a)
  rw [show j - a = q by omega] at hle this
  exact Finite.card_le_one_iff_subsingleton.1 hle

/-! ### Spreading out -/

section Spreading

/-- **The proper smooth model with an ample invertible sheaf.** A proper smooth scheme over a
field with an ample invertible sheaf is the base change of a proper smooth scheme over a
finitely generated `ℤ`-subalgebra of the field, carrying an ample invertible sheaf whose pullback
is the given one. -/
private theorem exists_isPullback_finiteType_properSmooth_isAmple {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ (R : Type u) (_ : CommRing R) (φ : R →+* k) (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R))
      (q' : X ⟶ Y) (LY : Y.Modules)
      (_ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 LY),
      Algebra.FiniteType ℤ R ∧ Function.Injective φ ∧ IsProper h ∧ Smooth h ∧
        IsPullback q' f h (Spec.map (CommRingCat.ofHom φ)) ∧ Stacks.Ample.IsAmple Y LY ∧
        Nonempty (L ≅ (Scheme.Modules.pullback q').obj LY) := by
  classical
  obtain ⟨j₀, Y₀, h₀, q₀, hpr₀, hsm₀, hpb₀⟩ :=
    HodgeSpreadingOut.exists_isPullback_affineStageCone_properSmooth f
  let D₀ := specAdjoinFinsetDiagram Γ(Spec (.of k), ⊤)
  let c₀ := affineStageCone (Spec (.of k))
  have hc₀ : IsLimit c₀ := isLimit_affineStageCone (Spec (.of k))
  -- the base changes of `Y₀` to the stages below `j₀`, and their limit
  let D : Over j₀ ⥤ Scheme.{u} := Over.post D₀ ⋙ Over.pullback h₀ ⋙ Over.forget Y₀
  let c : Cone D := (Over.forget Y₀).mapCone ((Over.pullback h₀).mapCone (c₀.overPost j₀))
  have hc : IsLimit c := isLimitOfPreserves _ (isLimitOfPreserves _ (hc₀.overPost j₀))
  have hD₀aff : ∀ {i i' : (Finset Γ(Spec (.of k), ⊤))ᵒᵖ} (g : i ⟶ i'), IsAffineHom (D₀.map g) :=
    fun g => by change IsAffineHom (Spec.map _); infer_instance
  haveI hDaff : ∀ {t t' : Over j₀} (g : t ⟶ t'), IsAffineHom (D.map g) := fun {t t'} g =>
    MorphismProperty.overPullbackMap (P := @IsAffineHom) h₀ ((Over.post D₀).map g) (hD₀aff g.left)
  have hsnd : ∀ t : Over j₀, IsAffineHom (pullback.snd (D₀.map t.hom) h₀) := fun t =>
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _)
      (hD₀aff t.hom)
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace h₀
  haveI hY₀qs : QuasiSeparatedSpace Y₀ := by
    haveI := IsSeparated.instQuasiSeparated h₀
    exact quasiSeparatedSpace_of_quasiSeparated h₀
  haveI hDqc : ∀ t : Over j₀, CompactSpace (D.obj t) := fun t =>
    @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd (D₀.map t.hom) h₀)
      (@instQuasiCompactOfIsAffineHom _ _ _ (hsnd t)) _
  haveI hDqs : ∀ t : Over j₀, QuasiSeparatedSpace (D.obj t) := fun t =>
    @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (D₀.map t.hom) h₀) hY₀qs
      (@IsSeparated.instQuasiSeparated _ _ _ (@IsSeparated.of_isAffineHom _ _ _ (hsnd t)))
  -- the apex is `X`
  let e : X ≅ c.pt := hpb₀.flip.isoPullback
  -- descend `L`
  haveI hL' : SheafOfModules.IsInvertible c.pt.presheaf c.pt.ringCatSheaf.2
      ((Scheme.Modules.pullback e.inv).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback e.inv L
  obtain ⟨t₁, L₁, hL₁, ⟨eL₁⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit D c hc
      ((Scheme.Modules.pullback e.inv).obj L) hL'
  haveI : SheafOfModules.IsInvertible (D.obj t₁).presheaf (D.obj t₁).ringCatSheaf.2 L₁ := hL₁
  -- ampleness at the limit, then at a stage
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace c.pt := (Scheme.homeoOfIso e).compactSpace
  have hamp₀ : Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback e.inv).obj L) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom e.inv L
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL)
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback (c.π.app t₁) L₁
  have hamp₁ : Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback (c.π.app t₁)).obj L₁) := by
    rw [← Stacks.AmpleBridge.isAmple_iff_isAmple] at hamp₀ ⊢
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eL₁).1 hamp₀
  obtain ⟨t₂, g, hamp₂⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs D c hc t₁
      L₁ hamp₁
  -- the model at the stage `t₂`
  let R := Algebra.adjoin ℤ ((t₂.left.unop : Finset Γ(Spec (.of k), ⊤)) : Set Γ(Spec (.of k), ⊤))
  let φ : R →+* k := (Scheme.ΓSpecIso (.of k)).hom.hom.comp R.val.toRingHom
  have hπφ : c₀.π.app t₂.left = Spec.map (CommRingCat.ofHom φ) :=
    HodgeSpreadingOut.affineStageCone_π_app_spec (.of k) t₂.left
  let h : D.obj t₂ ⟶ Spec (.of R) := pullback.fst (D₀.map t₂.hom) h₀
  let q' : X ⟶ D.obj t₂ := e.hom ≫ c.π.app t₂
  let LY := (Scheme.Modules.pullback (D.map g)).obj L₁
  haveI hLY : SheafOfModules.IsInvertible (D.obj t₂).presheaf (D.obj t₂).ringCatSheaf.2 LY :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ L₁
  have hq'snd : q' ≫ pullback.snd (D₀.map t₂.hom) h₀ = q₀ := by
    simp only [q', e, c, Category.assoc]
    exact (congrArg (fun φ => hpb₀.flip.isoPullback.hom ≫ φ) (pullback.lift_snd _ _ _)).trans
      hpb₀.flip.isoPullback_hom_snd
  have hq'fst : q' ≫ h = f ≫ c₀.π.app t₂.left := by
    simp only [q', e, c, h, Category.assoc]
    refine (congrArg (fun φ => hpb₀.flip.isoPullback.hom ≫ φ) (pullback.lift_fst _ _ _)).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ((c₀.overPost j₀).π.app t₂).left) hpb₀.flip.isoPullback_hom_fst)
  have hsq : IsPullback q' f h (c₀.π.app t₂.left) := by
    refine IsPullback.of_right ?_ hq'fst (IsPullback.of_hasPullback (D₀.map t₂.hom) h₀).flip
    have hw : c₀.π.app t₂.left ≫ D₀.map t₂.hom = c₀.π.app j₀ := c₀.w t₂.hom
    rw [hq'snd]
    exact cast (congrArg (IsPullback q₀ f h₀) hw.symm) hpb₀
  -- `L ≅ q'^*L_Y`
  let eL : L ≅ (Scheme.Modules.pullback q').obj LY :=
    ((Scheme.Modules.pullbackId X).app L).symm ≪≫
      ((Scheme.Modules.pullbackCongr e.hom_inv_id).app L).symm ≪≫
      ((Scheme.Modules.pullbackComp e.hom e.inv).app L).symm ≪≫
      (Scheme.Modules.pullback e.hom).mapIso
        (eL₁ ≪≫ (Scheme.Modules.pullbackCongr (c.w g).symm).app L₁ ≪≫
          ((Scheme.Modules.pullbackComp (c.π.app t₂) (D.map g)).app L₁).symm) ≪≫
      (Scheme.Modules.pullbackComp e.hom (c.π.app t₂)).app LY
  have hhpr : IsProper h := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (D₀.map t₂.hom) h₀).flip hpr₀
  have hhsm : Smooth h := MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback (D₀.map t₂.hom) h₀).flip hsm₀
  exact ⟨R, inferInstance, φ, D.obj t₂, h, q', LY, hLY, finiteType_adjoinFinset_int _ _,
    fun _ _ hxy => Subtype.ext ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective hxy),
    hhpr, hhsm, hπφ ▸ hsq, (Stacks.AmpleBridge.isAmple_iff_isAmple _ LY).2 hamp₂, ⟨eL⟩⟩

/-- **The relative dimension spreads out.** If a smooth morphism `h : Y ⟶ Spec R` over a domain
becomes smooth of relative dimension `n` after the base change along `R ↪ k` to a field, then
`h` is smooth of relative dimension `n`: every connected component of `Y` dominates `Spec R`, so
meets the generic fibre, and the fibre dimension of a smooth morphism is locally constant. -/
private theorem smoothOfRelativeDimension_of_isPullback {R : Type u} [CommRing R] [IsDomain R]
    {k : Type u} [Field k] (φ : R →+* k) (hφ : Function.Injective φ) {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {h : Y ⟶ Spec (.of R)} {q' : X ⟶ Y}
    (hpb : IsPullback q' f h (Spec.map (CommRingCat.ofHom φ))) [Smooth h] (n : ℕ)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n h := by
  classical
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq h n fun y => ?_
  set F : Y → WithBot ℕ∞ := fun y => topologicalKrullDimAt (h.fiber (h y)) (h.asFiber y) with hFdef
  have hWo : IsOpen {y' | F y' = F y} :=
    (isLocallyConstant_fiberDimensionAt h (syntomic_of_smooth h)).isOpen_fiber (F y)
  have himg : IsOpen (h.base '' {y' | F y' = F y}) := h.isOpenMap _ hWo
  let ptk : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ s : Spec (.of R), (Spec.map (CommRingCat.ofHom φ)).base ptk ⤳ s := fun s =>
    (PrimeSpectrum.le_iff_specializes _ _).mp (by
      change Ideal.comap φ ⊥ ≤ s.asIdeal
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
      exact bot_le)
  obtain ⟨y', hy'F, hy'η⟩ := (hη (h y)).mem_open himg ⟨y, rfl, rfl⟩
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback y' ptk hy'η
  have hx : q' (hpb.isoPullback.inv z) = y' := by
    rw [← hz₁, ← hpb.isoPullback_inv_fst]
    rfl
  change F y = n
  rw [← show F y' = F y from hy'F, ← hx]
  exact (topologicalKrullDimAt_fiber_eq_of_isPullback hpb _).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension f n _)

/-- **Pullback of `Ω^a ⊗ L^{-1}`.** For a cartesian square and `L` invertible,
`g'^*(Ω^a_{X/S} ⊗ L^{-1}) ≅ Ω^a_{X'/S'} ⊗ (g'^*L)^{-1}`. -/
private theorem nonempty_iso_pullback_formsTensor_dualSheaf {X S X' S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g) (a : ℕ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Nonempty ((Scheme.Modules.pullback g').obj
        (formsTensor f a (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) ≅
      formsTensor f' a (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Scheme.Modules.pullback g').obj L))) := by
  let eΩ : (Scheme.Modules.pullback g').obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a) ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f') a :=
    @asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w (a : ℤ))
      (Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g' f f' g hsq (a : ℤ))
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g' L
  haveI := isInvertible_dualSheaf L
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g'
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)
  obtain ⟨eD⟩ : Nonempty ((Scheme.Modules.pullback g').obj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Scheme.Modules.pullback g').obj L)) := by
    refine (pic_eq_iff _ _
      (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g' _)
      (isInvertible_dualSheaf _)).1 ?_
    rw [pic_dualSheaf]
    have h₁ : pic ((Scheme.Modules.pullback g').obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L))
          (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g' _) =
        Stacks.Picard.schemePullbackClass g' (pic _ (isInvertible_dualSheaf L)) :=
      (Stacks.Picard.pullbackClass_classOf g'.toLRSHom.toShHom
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) (isInvertible_dualSheaf L)).symm
    have h₂ : pic ((Scheme.Modules.pullback g').obj L)
          (Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g' L) =
        Stacks.Picard.schemePullbackClass g'
          (pic L ‹SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L›) :=
      (Stacks.Picard.pullbackClass_classOf g'.toLRSHom.toShHom L
        ‹SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L›).symm
    rw [h₁, h₂, pic_dualSheaf]
    exact map_neg (Stacks.Picard.pullbackClassHom g'.toLRSHom.toShHom) _
  exact ⟨(Stacks.RingedSpace.comparisonBifunctorIso g'.toLRSHom.toShHom).app
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a,
        Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.toRingedSpace.sheaf).mapIso
      eΩ).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.toRingedSpace.sheaf).obj
      _).mapIso eD⟩

section Semicontinuity

attribute [local instance 10000] HasDerivedCategory.standard

open ProperFlatFibreEulerCharacteristic in
/-- **The derived-fibre Betti numbers of `Rh_*G` are the dimensions of the cohomology of the
fibres.** For `h` proper and flat of finite presentation and `G` of finite presentation and flat
over the base, and a cartesian square with a field `K`, the `m`-th derived-fibre Betti number of
`Rh_*G` at the image of the point of `Spec K` is `dim_K H^m(X, g'^*G)`. -/
private theorem derivedFiberBetti_derivedPushforwardModule_eq_finrank {Y S : Scheme.{u}}
    (h : Y ⟶ S) [IsProper h] [Flat h] [LocallyOfFinitePresentation h] (G : Y.Modules)
    (hGfp : G.IsFinitePresentation) (hGqc : SheafOfModules.IsQuasicoherent G)
    (hflat : IsFlatOver h.toLRSHom.toShHom G)
    (hE : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G))
    (K : Type u) [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} {g' : X ⟶ Y}
    {g : Spec (.of K) ⟶ S} (hsq : IsPullback g' f h g) (m : ℕ) (pt : Spec (.of K)) :
    DerivedFibreBetti.derivedFiberBetti S
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) hE m (g.base pt) =
      Module.finrank K (cohomologyOverField K f ((Scheme.Modules.pullback g').obj G) m) := by
  have : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : Flat f := MorphismProperty.of_isPullback (P := @Flat) hsq inferInstance
  refine (congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback g
    (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) hE m) pt).symm.trans ?_
  have hqc : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pullback g').obj G) := by
    haveI := Stacks.Modules.isFinitePresentation_pullback g' G hGfp
    infer_instance
  haveI hqcH : QuasiCompact h := inferInstance
  haveI hsepH : IsSeparated h := inferInstance
  haveI hqsH : QuasiSeparated h := IsSeparated.instQuasiSeparated h
  obtain ⟨e⟩ :=
    @nonempty_derivedPullback_derivedPushforward_singleFunctor_iso
      Y S X (Spec (.of K)) h g f g' hsq hqcH hqsH G hGqc hqc hflat
  have hFfp : ((Scheme.Modules.pullback g').obj G).IsFinitePresentation :=
    Stacks.Modules.isFinitePresentation_pullback g' G hGfp
  have hE' : RingedSpace.IsPseudoCoherent (X := (Spec (.of K)).toRingedSpace)
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule f
        ((Scheme.Modules.pullback g').obj G)) :=
    Scheme.Modules.isPseudoCoherent_of_isPerfect _
      (ProperFlatFibreEulerCharacteristic.isPerfect_derivedPushforward_singleFunctor_of_isProper f
        ⟨inferInstance, inferInstance, inferInstance⟩ inferInstance _ hFfp
        (AlgebraicGeometry.isFlatOver_of_field K f _))
  exact (congrFun (FibreBetti.derivedFiberBetti_eq_of_iso _ _ hE' e m) pt).trans
    (DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule K f _ hE' m pt)

/-- **Upper semicontinuity of cohomology in a proper flat family.** Let `h : Y ⟶ Spec R` be proper
and flat of finite presentation over a domain and `G` a module of finite presentation on `Y`,
flat over `R`. If the fibre of `G` over a point `s` has vanishing `H^q`, so has the base change
of `G` to any field into which `R` embeds. -/
private theorem subsingleton_H_pullback_of_subsingleton_H_fibre {R : Type u} [CommRing R]
    [IsDomain R] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) [IsProper h] [Smooth h] (G : Y.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    {k : Type u} [Field k] (φ : R →+* k) (hφ : Function.Injective φ) {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {q' : X ⟶ Y} (hpb : IsPullback q' f h (Spec.map (CommRingCat.ofHom φ)))
    {κ : Type u} [Field κ] (ψ : R →+* κ) {V : Scheme.{u}} {fV : V ⟶ Spec (.of κ)} {j : V ⟶ Y}
    (hsq : IsPullback j fV h (Spec.map (CommRingCat.ofHom ψ))) (q : ℤ)
    (hV : Subsingleton (H fV ((Scheme.Modules.pullback j).obj G) q)) :
    Subsingleton (H f ((Scheme.Modules.pullback q').obj G) q) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact subsingleton_H_of_neg f _ hq
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  have hGfp : G.IsFinitePresentation := Stacks.Chow.isFinitePresentation_of_isFiniteLocallyFree G hG
  have hGqc : SheafOfModules.IsQuasicoherent G := inferInstance
  haveI := hG
  have hflat : IsFlatOver h.toLRSHom.toShHom G :=
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h G
  have hfp : FinitePresentation h := ⟨inferInstance, inferInstance, inferInstance⟩
  have hE : RingedSpace.IsPseudoCoherent (X := (Spec (.of R)).toRingedSpace)
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) :=
    Scheme.Modules.isPseudoCoherent_of_isPerfect _
      (ProperFlatFibreEulerCharacteristic.isPerfect_derivedPushforward_singleFunctor_of_isProper h
        hfp inferInstance G hGfp hflat)
  let ptk : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  let ptκ : Spec (.of κ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη := derivedFiberBetti_derivedPushforwardModule_eq_finrank h G hGfp hGqc hflat hE k hpb
    m ptk
  have hs := derivedFiberBetti_derivedPushforwardModule_eq_finrank h G hGfp hGqc hflat hE κ hsq
    m ptκ
  -- the image of the point of `Spec k` is the generic point, which specializes to everything
  have hgen :
      (Spec.map (CommRingCat.ofHom φ)).base ptk ⤳ (Spec.map (CommRingCat.ofHom ψ)).base ptκ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
    change Ideal.comap φ ⊥ ≤ Ideal.comap ψ ⊥
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  have hle : DerivedFibreBetti.derivedFiberBetti (Spec (.of R))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) hE m
        ((Spec.map (CommRingCat.ofHom φ)).base ptk) ≤
      DerivedFibreBetti.derivedFiberBetti (Spec (.of R))
        (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) hE m
        ((Spec.map (CommRingCat.ofHom ψ)).base ptκ) := by
    set β := DerivedFibreBetti.derivedFiberBetti (Spec (.of R))
      (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule h G) hE m
    have husc : UpperSemicontinuous β :=
      DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti _ _ _ _
    have hev : ∀ᶠ y in nhds ((Spec.map (CommRingCat.ofHom ψ)).base ptκ),
        β y < β ((Spec.map (CommRingCat.ofHom ψ)).base ptκ) + 1 :=
      husc _ _ (Nat.lt_succ_self _)
    exact Nat.lt_succ_iff.mp (show ∀ᶠ y in nhds ((Spec.map (CommRingCat.ofHom φ)).base ptk),
      β y < β ((Spec.map (CommRingCat.ofHom ψ)).base ptκ) + 1 from hgen hev).self_of_nhds
  haveI : Subsingleton (cohomologyOverField κ fV ((Scheme.Modules.pullback j).obj G) m) :=
    @Equiv.subsingleton _ _
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField κ fV _ m).toEquiv hV
  have h0 : Module.finrank κ (cohomologyOverField κ fV ((Scheme.Modules.pullback j).obj G) m) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hk :
      Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pullback q').obj G) m) = 0 := by
    omega
  -- finite dimensionality, and conclusion
  have : IsProper f := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : SheafOfModules.IsCoherent ((Scheme.Modules.pullback q').obj G) :=
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation _).2
      (Stacks.Modules.isFinitePresentation_pullback q' G hGfp)
  haveI := finiteDimensional_cohomologyOverField_of_isProper k f
    ((Scheme.Modules.pullback q').obj G) m
  haveI : Subsingleton (cohomologyOverField k f ((Scheme.Modules.pullback q').obj G) m) :=
    Module.finrank_zero_iff.mp hk
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
    m).toEquiv.symm.subsingleton

end Semicontinuity

end Spreading

/-- **Spreading out.** A proper smooth scheme of relative dimension `n` over a field of
characteristic zero with an ample invertible sheaf has a fibre over a finite field of
characteristic `p > n`, with a `W₂`-lift and an ample invertible sheaf, whose vanishing of
`H^q(Ω^a ⊗ (-)^{-1})` implies that of `X`. -/
private theorem exists_finite_fibre {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F p),
      n < p ∧ ∃ (V : Scheme.{u}) (fV : V ⟶ Spec (.of F)) (_ : IsProper fV)
        (_ : SmoothOfRelativeDimension n fV) (𝒱 : Scheme.{u})
        (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F))) (_ : SmoothOfRelativeDimension n g)
        (π : TruncatedWittVector p 2 F →+* F) (_ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
        (_ : IsPullback i fV g (Spec.map (CommRingCat.ofHom π))) (N : V.Modules)
        (_ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 N)
        (_ : Stacks.Ample.IsAmple V N),
        ∀ (a : ℕ) (q : ℤ),
          Subsingleton (H fV (formsTensor fV a
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf N)) q) →
          Subsingleton (H f (formsTensor f a
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) q) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  -- step 1: the model over a finitely generated `ℤ`-algebra
  obtain ⟨R, _, φ, Y, h, q', LY, _, hft, hinj, hpr, hsm, hpb, hLY, ⟨eL⟩⟩ :=
    exists_isPullback_finiteType_properSmooth_isAmple f L hL
  have : IsDomain R := hinj.isDomain φ
  have : CharZero R := ⟨fun a b hab => Nat.cast_injective (R := k) (by
    rw [← map_natCast φ a, ← map_natCast φ b, hab])⟩
  have : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp hft
  haveI := smoothOfRelativeDimension_of_isPullback φ hinj hpb n
  -- step 2: a closed point with finite residue field of large characteristic in the smooth locus
  obtain ⟨s, hsU, hsmax, hsfin, hsN⟩ := HodgeSpreadingOut.exists_isMaximal_finite_lt_ringChar R
    Algebra.isOpen_smoothLocus
    ⟨⟨⊥, Ideal.isPrime_bot⟩, HodgeSpreadingOut.mem_smoothLocus_int_bot R⟩ n
  set κ := s.asIdeal.ResidueField
  set p := ringChar κ
  have hp : p.Prime := (CharP.char_is_prime_or_zero κ p).resolve_right (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  -- the fibre at `s`
  let gs : Spec (.of κ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  have hsq : IsPullback (pullback.fst h gs) (pullback.snd h gs) h gs :=
    IsPullback.of_hasPullback h gs
  -- step 3: the lift over `W₂(κ)`
  obtain ⟨ψ, hψ⟩ := HodgeSpreadingOut.exists_wittTwo_lift R hsU p
  let gW : Spec (.of (TruncatedWittVector p 2 κ)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ψ)
  let πs : Spec (.of κ) ⟶ Spec (.of (TruncatedWittVector p 2 κ)) :=
    Spec.map (CommRingCat.ofHom (HodgeSpreadingOut.wittTwoToField p κ))
  have hcomp : πs ≫ gW = gs := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  have hW : IsPullback (pullback.fst h gW) (pullback.snd h gW) h gW :=
    IsPullback.of_hasPullback h gW
  have hcond : pullback.fst h gs ≫ h = (pullback.snd h gs ≫ πs) ≫ gW := by
    rw [Category.assoc, hcomp, pullback.condition]
  have hlift : IsPullback (pullback.lift (pullback.fst h gs) (pullback.snd h gs ≫ πs) hcond)
      (pullback.snd h gs) (pullback.snd h gW) πs := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hW
    rw [pullback.lift_fst, hcomp]
    exact hsq
  -- the ample invertible sheaf on the fibre
  haveI : IsAffineHom (pullback.fst h gs) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip inferInstance
  let N := (Scheme.Modules.pullback (pullback.fst h gs)).obj LY
  haveI hNinv : SheafOfModules.IsInvertible (pullback h gs).presheaf
      (pullback h gs).ringCatSheaf.2 N :=
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ LY
  have hN : Stacks.Ample.IsAmple (pullback h gs) N := by
    haveI : CompactSpace (pullback h gs : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd h gs)
    rw [Stacks.AmpleBridge.isAmple_iff_isAmple] at hLY ⊢
    exact AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isAffineHom _ LY hLY
  have hVsm : SmoothOfRelativeDimension n (pullback.snd h gs) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback hsq inferInstance
  have hWsm : SmoothOfRelativeDimension n (pullback.snd h gW) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback hW inferInstance
  refine ⟨p, ⟨hp⟩, κ, inferInstance, hsfin, inferInstance, hsN, pullback h gs, pullback.snd h gs,
    inferInstance, hVsm, pullback h gW, pullback.snd h gW, hWsm,
    HodgeSpreadingOut.wittTwoToField p κ, fun x => rfl, _, hlift, N, hNinv, hN, ?_⟩
  -- step 4: transport the vanishing
  intro a q hV
  obtain ⟨e₁⟩ := nonempty_iso_pullback_formsTensor_dualSheaf hpb a LY
  obtain ⟨e₂⟩ := nonempty_iso_pullback_formsTensor_dualSheaf hsq a LY
  haveI := isInvertible_dualSheaf LY
  have hG := isFiniteLocallyFree_formsTensor h n
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf LY) a
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback q' LY
  haveI := isInvertible_dualSheaf ((Scheme.Modules.pullback q').obj LY)
  haveI := isInvertible_dualSheaf L
  -- `L^{-1} ≅ (q'^*L_Y)^{-1}`, by comparing Picard classes
  obtain ⟨eD⟩ : Nonempty (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Scheme.Modules.pullback q').obj LY)) := by
    refine (pic_eq_iff _ _ (isInvertible_dualSheaf L) (isInvertible_dualSheaf _)).1 ?_
    rw [pic_dualSheaf, pic_dualSheaf, (pic_eq_iff _ _ _ _).2 ⟨eL⟩]
  haveI : Subsingleton (H (pullback.snd h gs) ((Scheme.Modules.pullback (pullback.fst h gs)).obj
      (formsTensor h a (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf LY))) q) :=
    @subsingleton_H_congr _ _ _ _ _ _ e₂ q hV
  exact @subsingleton_H_congr _ _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
      _).mapIso eD ≪≫ e₁.symm) q
    (subsingleton_H_pullback_of_subsingleton_H_fibre h _ hG φ hinj hpb (algebraMap R κ) hsq q
      this)

/-- **Akizuki--Nakano vanishing.** Let `X` be a smooth projective variety of dimension `n` over a
field `k` of characteristic zero and `L` an ample invertible sheaf on `X`. Then
`H^q(X, Ω_X^a ⊗ L^{-1}) = 0` whenever `a + q < n`, where `Ω_X^a = ⋀^a Ω_{X/k}`. -/
@[mmp "thm_mmp_conductor_negative_nakano"]
public theorem subsingleton_derivedCohomologyOverField_exteriorPower_tensor_dualSheaf_of_isAmple
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (hsm : IsSmoothScheme f) (n : ℕ) (hn : topologicalKrullDim X = n)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Stacks.Ample.IsAmple X L) (a : ℕ) (q : ℤ) (haq : (a : ℤ) + q < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)).obj
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L))) q) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f ‹IsProjectiveVariety k f›.isProjective
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  haveI := smoothOfRelativeDimension_of_equidimensional k f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) n hn
  obtain ⟨p, _, F, _, _, _, hpn, V, fV, _, _, 𝒱, g, _, π, hπ, i, hi, N, _, hN, htr⟩ :=
    exists_finite_fibre f n L hL
  exact htr a q (subsingleton_H_formsTensor_dualSheaf_of_finite p n hpn fV g π hπ i hi N hN a q haq)

end MMP.Mori
