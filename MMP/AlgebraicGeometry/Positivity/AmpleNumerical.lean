module

public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentChartDictionary
public import MMP.AlgebraicGeometry.Positivity.BigAmplePlusEffective
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity

/-!
# Ample plus nef is ample, and nef and big divisors are ample up to a small effective part

Let `X` be a normal projective variety over a field `k`.

First, ampleness is numerical and stable under adding nef classes: if `A` is an ample
`ℚ`-divisor, `N` a nef `ℚ`-divisor and `B ≡ A + N`, then for every `m > 0` such that `mB` is a
Cartier divisor `D`, the invertible sheaf `𝒪_X(D)` is ample. Choose `a > 0` with `aA` an ample
Cartier divisor `D_A`. Then `L = aD - mD_A` is a nef Cartier divisor, of degree `am (N · C)` on
every curve `C`, and `𝒪_X(aD) ≅ 𝒪_X(mD_A) ⊗ 𝒪_X(L)`. On a projective scheme over a field an
ample sheaf tensored with a nef one is ample by the Nakai criterion: the multilinear expansion of
`((mD_A + L)^d · V)` has nonnegative mixed terms by Kleiman's theorem, so
`((aD)^d · V) ≥ ((mD_A)^d · V) > 0`. Finally `𝒪_X(D)` is ample because its power `𝒪_X(aD)` is.

Second, if `D` is a nef and big Cartier divisor, there are an effective Cartier divisor `E`, an
integer `k₀ > 0` and ample `ℚ`-divisors `Aₙ` with `D ≡ Aₙ + (1/n) E` for every `n ≥ k₀`. By
Kodaira's lemma some multiple `mD` has `𝒪_X(mD) ≅ 𝒪_X(A + E)` with `A` ample and `E` effective
Cartier; for `n ≥ m` take `Aₙ = (1/n)(A + (n - m)D)`, which is ample since `(n - m)D` is nef.

## Main results

* `MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef`: ample plus nef is ample.
* `MMP.Mori.exists_numericallyEquivalent_isAmple_add_smul`: Kollár–Mori 2.61 (1) ⇒ (3).

## Implementation notes

The source deduces the first result from Kleiman's criterion on the closed cone of curves. Here
the Nakai criterion is applied directly to `𝒪_X(mD_A) ⊗ 𝒪_X(L)`, which needs no cone of curves
and works over an arbitrary base field.

Kodaira's lemma is available for Cartier divisors `X.CartierDivisor`; the Weil divisor `D` is
first replaced by a Cartier divisor with isomorphic invertible sheaf, and the divisors `A`, `E`
it produces are carried back to Weil divisors through their divisors of orders.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.18, 1.37,
  2.61
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

section AmpleNumerical

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-! ### Intersection numbers on a closed subscheme -/

section Restrict

open Stacks.SheafOfModules.Invertible

/-- Integer tensor powers depend only on the isomorphism class of the invertible module. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{0}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  Stacks.Equivalence.powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, 0, 0, 0}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- Isomorphic families of invertible modules give isomorphic twists. -/
private noncomputable def twistListFamilyIso {X : Scheme.{0}} {r : ℕ} (L L' : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' i)]
    (e : ∀ i, L i ≅ L' i) (n : Fin r → ℤ) :
    ∀ (l : List (Fin r)) {M M' : X.Modules}, (M ≅ M') →
      (twistList L n l M ≅ twistList L' n l M')
  | [], _, _, ε => ε
  | i :: t, _, _, ε => twistListFamilyIso L L' e n t
      (tensorProductIso X.presheaf X.ringCatSheaf.2 ε
        (tensorPowerIsoOfIso (L i) (L' i) (e i) (n i)))

/-- Intersection numbers along a closed subscheme are computed on it. -/
private theorem intersectionNumber_pullback_comp (k : Type) [Field k] {X W Z : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : W ⟶ X) [IsClosedImmersion i] (j : Z ⟶ W)
    [IsClosedImmersion j] (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k (i ≫ f) j d hd (fun q => (Scheme.Modules.pullback i).obj (L q)) =
      intersectionNumber k f (j ≫ i) d hd L := by
  unfold intersectionNumber
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  refine finsum_congr fun n => ?_
  congr 2
  rw [← Category.assoc]
  exact finrank_cohomologyOverField_eq_of_iso k _
    (twistListFamilyIso (fun q => (Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback i).obj (L q)))
      (fun q => (Scheme.Modules.pullback (j ≫ i)).obj (L q))
      (fun q => (Scheme.Modules.pullbackComp j i).app (L q)) _ _ (Iso.refl _)) n

private theorem intersectionNumber_congr_immersion (k : Type) [Field k] {X Z : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {i i' : Z ⟶ X} [IsClosedImmersion i]
    [IsClosedImmersion i'] (h : i = i') (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L = intersectionNumber k f i' d hd L := by
  subst h; rfl

end Restrict

/-! ### Expanding `(A ⊗ L)^d` -/

/-- The family with `M` in the slots of `S` and `F` elsewhere. -/
private def selFam {X : Scheme.{0}} {d : ℕ} (S : Finset (Fin d)) (M : X.Modules)
    (F : Fin d → X.Modules) : Fin d → X.Modules := fun q => if q ∈ S then M else F q

private theorem selFam_of_mem {X : Scheme.{0}} {d : ℕ} {S : Finset (Fin d)} {M : X.Modules}
    {F : Fin d → X.Modules} {q : Fin d} (h : q ∈ S) : selFam S M F q = M := if_pos h

private theorem selFam_of_notMem {X : Scheme.{0}} {d : ℕ} {S : Finset (Fin d)} {M : X.Modules}
    {F : Fin d → X.Modules} {q : Fin d} (h : q ∉ S) : selFam S M F q = F q := if_neg h

private theorem isInvertible_selFam {X : Scheme.{0}} {d : ℕ} (S : Finset (Fin d)) (M : X.Modules)
    (F : Fin d → X.Modules) [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hF : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F q)] (q : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (selFam S M F q) := by
  unfold selFam
  split_ifs <;> infer_instance

attribute [local instance] isInvertible_selFam

/-- If `P ≅ A ⊗ L` and every mixed intersection number `(L^{|T|} · A^{d - |T|} · V)` is
nonnegative, then `(A^d · V) ≤ (P^d · V)`. -/
private theorem intersectionNumber_le_of_iso_tensor (κ : Type) [Field κ] {F V : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) [IsProper g] (i : V ⟶ F) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim V ≤ d) (A L P : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 P]
    (e : P ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨F.presheaf, F.IsSheaf⟩).obj A).obj L)
    (hmix : ∀ T : Finset (Fin d),
      0 ≤ intersectionNumber κ g i d hd (selFam T L fun _ => A)) :
    intersectionNumber κ g i d hd (fun _ => A) ≤ intersectionNumber κ g i d hd (fun _ => P) := by
  classical
  have key : ∀ S T : Finset (Fin d), Disjoint S T →
      intersectionNumber κ g i d hd (selFam T L fun _ => A) ≤
        intersectionNumber κ g i d hd (selFam S P (selFam T L fun _ => A)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro T _
      exact le_of_eq (intersectionNumber_congr_family κ g i d hd (funext fun q =>
        (selFam_of_notMem (Finset.notMem_empty q)).symm))
    | insert a s ha ih =>
      intro T hdisj
      have haT : a ∉ T := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a s)
      have hs : Disjoint s T := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hdisj
      have hs' : Disjoint s (insert a T) := Finset.disjoint_insert_right.mpr ⟨ha, hs⟩
      have h := intersectionNumber_tensor κ g i d hd a
        (selFam (insert a s) P (selFam T L fun _ => A))
        (selFam s P (selFam T L fun _ => A))
        (selFam s P (selFam (insert a T) L fun _ => A))
        (fun q hq => by simp [selFam, Finset.mem_insert, hq])
        (fun q hq => by simp [selFam, Finset.mem_insert, hq])
        (eqToIso (by simp [selFam]) ≪≫ e ≪≫ eqToIso (by simp [selFam, ha, haT] <;> rfl))
      rw [h]
      linarith [ih T hs, ih (insert a T) hs', hmix (insert a T)]
  have := key Finset.univ ∅ (Finset.disjoint_empty_right _)
  refine le_of_eq_of_le (intersectionNumber_congr_family κ g i d hd (funext fun q => ?_))
    (this.trans_eq (intersectionNumber_congr_family κ g i d hd (funext fun q => ?_)))
  · exact (selFam_of_notMem (M := L) (F := fun _ => A) (Finset.notMem_empty q)).symm
  · exact selFam_of_mem (Finset.mem_univ q)

/-! ### Ample plus nef is ample on a projective scheme over a field -/

private theorem isProjective_comp {X Z S : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (hf : IsProjective f) : IsProjective (i ≫ f) := by
  obtain ⟨E, h1, h2, hqc, i', hi', hcomp⟩ := hf
  exact ⟨E, h1, h2, hqc, i ≫ i', inferInstance, by rw [Category.assoc, hcomp]⟩

/-- Nefness restricts to closed subschemes. -/
private theorem isNef_pullback (κ : Type) [Field κ] {F W : Scheme.{0}} (g : F ⟶ Spec (.of κ))
    (iW : W ⟶ F) [IsClosedImmersion iW] (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (hL : IsNef κ g L) :
    IsNef κ (iW ≫ g) ((Scheme.Modules.pullback iW).obj L) := by
  intro C c _ _ _ hC
  haveI : IsProper ((c ≫ iW) ≫ g) := by rw [Category.assoc]; infer_instance
  rw [degreeOn_pullback_eq_degreeOn_comp (iW ≫ g) g iW c rfl hC.le L]
  exact hL C (c ≫ iW) hC

/-- **Kleiman's theorem on closed subschemes.** On a projective `κ`-scheme a nef invertible sheaf
has nonnegative degree `(L^j · W)` on every integral closed subscheme `W` of dimension `j`. -/
private theorem intersectionNumber_nonneg_of_isNef (κ : Type) [Field κ] {F : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) (hg : IsProjective g) (L : F.Modules)
    [SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2 L] (hL : IsNef κ g L)
    (W : Scheme.{0}) (iW : W ⟶ F) [IsClosedImmersion iW] [IsIntegral W] (j : ℕ)
    (hW : topologicalKrullDim W = j) :
    haveI := hg.isProper
    0 ≤ intersectionNumber κ g iW j hW.le (fun _ => L) := by
  haveI := hg.isProper
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact (intersectionNumber_pos_of_topologicalKrullDim_eq_zero κ g iW hW _).le
  have hproj : MMP.Mori.IsProjectiveVariety κ (iW ≫ g) := by
    refine (MMP.Mori.isProjectiveVariety_iff κ _).2 ⟨(MMP.Mori.isVariety_iff κ _).2
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, ?_⟩
    exact isProjectiveMorphism_of_isProjective_of_isAffine _ (isProjective_comp iW g hg)
  have h := MMP.Mori.sheafSelfIntersectionNumber_nonneg_of_isNef κ (iW ≫ g) hproj
    ((Scheme.Modules.pullback iW).obj L) (isNef_pullback κ g iW L hL) W (𝟙 W) hW
  unfold sheafSelfIntersectionNumber at h
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_pullback_comp κ g iW (𝟙 W),
    intersectionNumber_congr_immersion κ g (Category.id_comp iW)] at h
  exact h

/-- **Ample plus nef is ample.** On a projective scheme `F` over a field `κ`, if `A` is ample and
`L` is nef, then every `P ≅ A ⊗ L` is ample. -/
private theorem isAmple_of_iso_tensor (κ : Type) [Field κ] {F : Scheme.{0}}
    (g : F ⟶ Spec (.of κ)) (hg : IsProjective g) (A L P : F.Modules) [IsInvertibleModule F A]
    [IsInvertibleModule F L] [IsInvertibleModule F P] (hA : IsAmple F A) (hL : IsNef κ g L)
    (e : P ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨F.presheaf, F.IsSheaf⟩).obj A).obj L) :
    IsAmple F P := by
  haveI := hg.isProper
  refine isAmple_of_sheafSelfIntersectionNumber_pos_of_dim_pos κ g hg P
    fun V i _ _ d hd hd0 => ?_
  have hpos := MMP.Threefold.Mori.sheafSelfIntersectionNumber_pos_of_isAmple κ g A hA V i d hd
  unfold sheafSelfIntersectionNumber at hpos ⊢
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber] at hpos ⊢
  refine hpos.trans_le (intersectionNumber_le_of_iso_tensor κ g i d _ A L P e fun T => ?_)
  exact MMP.Threefold.Mori.intersectionNumber_nonneg_of_isAmple_of_forall_eq_or_eq κ g L A hA
    (fun j W iW _ _ hW => intersectionNumber_nonneg_of_isNef κ g hg L hL W iW j hW) i d _ _
    fun q => by unfold selFam; split_ifs <;> simp

/-! ### Multiples of Cartier divisors -/

/-- `𝒪_X(nD) ≅ 𝒪_X(D)^{⊗ n}` for a Cartier divisor `D`. -/
private noncomputable def divisorialSheafNsmulIso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) (n : ℕ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    (n • D).divisorialSheaf ≅ tensorPowModule X D.divisorialSheaf (n : ℤ) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (tensorPowModuleZeroIso X D.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hD.nsmul n).divisorialSheafTensorIso hD).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (tensorPowModuleOneIso X D.divisorialSheaf).symm ≪≫
      tensorPowModuleAddIso X D.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- A Cartier divisor `D` is ample if and only if a positive multiple `nD` is. -/
private theorem isAmple_nsmul_iff {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D : Divisor X} (hD : D.IsCartier) {n : ℕ} (hn : 0 < n) :
    (n • D).IsAmple (hD.nsmul n) ↔ D.IsAmple hD := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := (hD.nsmul n).isInvertibleModule_divisorialSheaf
  unfold Divisor.IsAmple
  rw [isAmple_congr _ _ (divisorialSheafNsmulIso hD n),
    ← Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn]

/-! ### Numerically ample plus nef -/

/-- If `B ≡ A + N` with `N` nef, and `E`, `E'` are Cartier divisors with `E = nB` and `E' = nA`
as `ℚ`-divisors for some `n > 0`, then `E - E'` is nef. -/
private theorem isNef_sub_of_numericallyEquivalent_add (k : Type) [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {A N B : QDivisor X} (hA : A.IsQCartier) (hN : N.IsNef k sX)
    (hB : B.NumericallyEquivalent k sX (A + N)) {n : ℕ} (hn : 0 < n) {E E' : Divisor X}
    (hE : E.IsCartier) (hE' : E'.IsCartier) (hEB : Divisor.toQDivisor E = (n : ℤ) • B)
    (hEA : Divisor.toQDivisor E' = (n : ℤ) • A) : (E - E').IsNef k sX := by
  obtain ⟨hBq, hANq, hBeq⟩ := hB
  obtain ⟨hNq, hNnef⟩ := hN
  refine ⟨hE.sub hE', fun C i _ _ _ hC => ?_⟩
  have hdeg := Divisor.degreeOn_add k sX i hC.le E' (E - E') hE' (hE.sub hE')
  rw [Divisor.degreeOn_congr (add_sub_cancel E' E) _ hE] at hdeg
  have h := hBeq C i hC
  rw [QDivisor.intersectionNumber_add' k sX i hC.le A N hA hNq hANq,
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le B hBq hn E hE hEB,
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le A hA hn E' hE' hEA,
    div_eq_iff (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)] at h
  have hdq : (E.degreeOn k sX i hC.le hE : ℚ) =
      E'.degreeOn k sX i hC.le hE' + (E - E').degreeOn k sX i hC.le (hE.sub hE') :=
    mod_cast hdeg
  have := mul_nonneg (hNnef C i hC) (Nat.cast_nonneg (α := ℚ) n)
  exact_mod_cast (show (0 : ℚ) ≤ (E - E').degreeOn k sX i hC.le (hE.sub hE') by linarith)

end AmpleNumerical

namespace QDivisor

/-- **Ampleness is numerical; ample plus nef is ample.** On a normal projective variety `X` over
`k`, let `A` be an ample `ℚ`-divisor, `N` a nef `ℚ`-divisor and `B` a `ℚ`-divisor numerically
equivalent to `A + N`. Then for every integer `m > 0` and every Cartier divisor `D` with
`D = m B`, the invertible sheaf `𝒪_X(D)` is ample. -/
@[mmp "lem_km2c_ample_numerical"]
public theorem isAmple_of_numericallyEquivalent_add_of_isNef {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [QuasiCompact sX]
    {A N B : QDivisor X} (hA : A.IsAmple) (hN : N.IsNef k sX)
    (hB : B.NumericallyEquivalent k sX (A + N))
    (m : ℕ) (hm : 0 < m) (D : Divisor X) (hD : Divisor.toQDivisor D = (m : ℚ) • B)
    (hDc : D.IsCartier) :
    D.IsAmple hDc := by
  obtain ⟨a, ha, DA, hDA, hDAc, hDAamp⟩ := hA
  have hAq : A.IsQCartier :=
    ⟨a, by exact_mod_cast ha.ne', ⟨DA, by rw [hDA, natCast_zsmul, Nat.cast_smul_eq_nsmul], hDAc⟩⟩
  have hEBc : (a • D).IsCartier := hDc.nsmul a
  have hEAc : (m • DA).IsCartier := hDAc.nsmul m
  have hL := isNef_sub_of_numericallyEquivalent_add k sX hAq hN hB (Nat.mul_pos ha hm) hEBc hEAc
    (by rw [map_nsmul, hD, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ a,
      ← Nat.cast_smul_eq_nsmul ℚ (a * m), smul_smul]; push_cast; rfl)
    (by rw [map_nsmul, hDA, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ m,
      ← Nat.cast_smul_eq_nsmul ℚ (a * m), smul_smul]; push_cast; rw [mul_comm])
  have hLc : (a • D - m • DA).IsCartier := hEBc.sub hEAc
  -- `𝒪_X(aD) ≅ 𝒪_X(mD_A) ⊗ 𝒪_X(L)` is ample
  haveI := hEAc.isInvertibleModule_divisorialSheaf
  haveI := hEBc.isInvertibleModule_divisorialSheaf
  haveI := hLc.isInvertibleModule_divisorialSheaf
  refine (isAmple_nsmul_iff hDc ha).mp (isAmple_of_iso_tensor k sX
    (IsProjectiveMorphism.isProjective (IsProjectiveVariety.isProjective (k := k))) _ _ _
    ((isAmple_nsmul_iff hDAc hm).mpr hDAamp) ((Divisor.isNef_iff k sX _ hLc).mp hL) ?_)
  exact eqToIso (congrArg Divisor.divisorialSheaf (add_sub_cancel _ _).symm) ≪≫
    (hEAc.divisorialSheafTensorIso hLc).symm

end QDivisor

section NefBig

/-! ### From Weil to Cartier divisors and back -/

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {k R : Type} [Field k] [CommRing R] (φ : k →+* R)
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- `h⁰` of a Cartier divisor `A` equals `h⁰` of a divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`. -/
private theorem cartierH0_eq_h0 {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] (A : X.CartierDivisor) (D : Divisor X)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    cartierH0 k sX A = D.h0 k sX :=
  finrank_compHom_eq (scalarsToGlobalSections k sX)
    (Scheme.Modules.sectionsLinearEquivOfIso e ⊤)

/-- For a Cartier divisor `A` and a Cartier divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`, the
isomorphisms `𝒪_X((n + 1) A) ≅ 𝒪_X((n + 1) D)`. -/
private noncomputable def sheafSuccNsmulIso {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (A : X.CartierDivisor) (D : Divisor X) (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    ∀ n : ℕ, MMP.CartierDivisor.sheaf ((n + 1) • A) ≅
      ((n + 1) • D).divisorialSheaf
  | 0 => eqToIso (by rw [zero_add, one_smul]) ≪≫ e ≪≫ eqToIso (by rw [zero_add, one_smul])
  | n + 1 => eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso ((n + 1) • A) A).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X (sheafSuccNsmulIso A D hD e n) e ≪≫
      (hD.nsmul (n + 1)).divisorialSheafTensorIso hD ≪≫ eqToIso (by rw [← succ_nsmul])

/-- `cartierWeilDivisor D` is the Weil divisor of orders of the Cartier divisor `D`. -/
private lemma isWeilDivisorOfCartier_cartierWeilDivisor {S : Scheme.{0}} [IsIntegral S]
    [IsNoetherian S] (D : S.CartierDivisor) :
    MMP.Intersection.IsWeilDivisorOfCartier D (weilDivisorEquivFinsupp (cartierWeilDivisor D)) := by
  intro P
  have hcoh : Order.coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  haveI : Ring.KrullDimLE 1
      (S.presheaf.stalk (MMP.Intersection.primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le hcoh.le
  obtain ⟨N, hN⟩ :=
    MMP.Intersection.exists_isOrderAlong D (MMP.Intersection.primeDivisorSubvariety P)
  convert hN using 1
  have hN' := hN
  unfold MMP.Intersection.IsOrderAlong at hN'
  dsimp only [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hN'
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, rfl⟩ := hN'
  change cartierMultiplicity D (MMP.Mori.PrimeDivisor.genericPoint P) = _
  rw [MMP.Intersection.cartierMultiplicity_eq_ord_of_isLocalEquationAt hg]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (S.presheaf.stalk _) S.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (S.presheaf.stalk _) S.functionField b =
      algebraMap (S.presheaf.stalk _) S.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      MMP.Intersection.totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rw [mul_comm]
    exact this
  have hTg := MMP.Intersection.totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := S.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a ha0, ord_algebraMap_stalk _ hcoh b hb0] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- Cartier divisors linearly equivalent have isomorphic sheaves. -/
private theorem nonempty_sheaf_iso_of_linearlyEquivalent {X : Scheme.{0}}
    {B B' : X.CartierDivisor} (h : MMP.Intersection.LinearlyEquivalent B B') :
    Nonempty (MMP.CartierDivisor.sheaf B ≅
      MMP.CartierDivisor.sheaf B') := by
  obtain ⟨c, hc⟩ := (MMP.Intersection.mem_principalSubgroup_iff).1 h
  have hB : B = B' + MMP.Intersection.principalDivisor c := by rw [hc]; abel
  subst hB
  exact ⟨(MMP.CartierDivisor.sheafAddPrincipalIso B' c).symm⟩

/-- **Kodaira's lemma for Weil divisors.** On a normal projective variety, a big Cartier divisor
`D` has a positive multiple `mD` with `𝒪_X(mD) ≅ 𝒪_X(A + E)`, `A` an ample Cartier divisor and
`E` an effective Cartier divisor. -/
private theorem exists_iso_divisorialSheaf_ample_add_effective {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [hX : MMP.Mori.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {D : Divisor X} (hD : D.IsCartier)
    (hbig : D.IsBig k sX) :
    ∃ m : ℕ, 0 < m ∧ ∃ (A E : Divisor X) (hA : A.IsCartier), A.IsAmple hA ∧ 0 ≤ E ∧
      E.IsCartier ∧ Nonempty ((m • D).divisorialSheaf ≅ (A + E).divisorialSheaf) := by
  haveI : IsIntegral X := hX.toIsIntegral
  letI : IsNoetherian X := ⟨⟩
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨d, hd, c, hc, k₀, hk⟩ := hbig
  have hinf : {m : ℕ | c * (m : ℝ) ^ d < (cartierH0 k sX (m • C) : ℝ)}.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun a => ⟨max k₀.toNat a + 1, ?_, by omega⟩
    have h := hk ((max k₀.toNat a + 1 : ℕ) : ℤ) (by omega)
    rw [natCast_zsmul] at h
    simp only [Set.mem_setOf_eq]
    rwa [cartierH0_eq_h0 sX _ _ (sheafSuccNsmulIso C D hD eC.symm _)]
  obtain ⟨m, hm, A', E', -, hA'amp, hE', hlin⟩ :=
    exists_linearlyEquivalent_ample_add_effective sX hX hd C ⟨c, hc, hinf⟩
  have hwA := isWeilDivisorOfCartier_cartierWeilDivisor A'
  have hwE := isWeilDivisorOfCartier_cartierWeilDivisor E'
  set wA : Divisor X := weilDivisorEquivFinsupp (cartierWeilDivisor A')
  set wE : Divisor X := weilDivisorEquivFinsupp (cartierWeilDivisor E')
  have hwAE : MMP.Intersection.IsWeilDivisorOfCartier (A' + E') (wA + wE) := fun P => by
    simpa [DivisorWithCoeffs.coeff_add] using (hwA P).add (hwE P)
  obtain ⟨eA⟩ := hwA.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨eAE⟩ := hwAE.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨eL⟩ := nonempty_sheaf_iso_of_linearlyEquivalent hlin
  have hcA : wA.IsCartier := hwA.isCartier
  haveI := hcA.isInvertibleModule_divisorialSheaf
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact ⟨j + 1, hm, wA, wE, hcA, (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).1 hA'amp,
    fun P => (hwE P).nonneg_of_isEffective hE', hwE.isCartier,
    ⟨(sheafSuccNsmulIso C D hD eC.symm j).symm ≪≫ eL ≪≫ eAE⟩⟩

/-- The degree of `𝒪_X(F)` along a curve only depends on the isomorphism class of `𝒪_X(F)`. -/
private theorem degreeOn_eq_of_iso_divisorialSheaf {k : Type} [Field k] {X Cv : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (i : Cv ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim Cv ≤ 1) {F F' : Divisor X}
    (hF : F.IsCartier) (hF' : F'.IsCartier) (e : F.divisorialSheaf ≅ F'.divisorialSheaf) :
    F.degreeOn k sX i hdim hF = F'.degreeOn k sX i hdim hF' := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hF.isInvertibleModule_divisorialSheaf
  haveI := hF'.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim e

/-- A nonnegative multiple of a nef Cartier divisor is nef. -/
private theorem isNef_nsmul {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X} (hD : D.IsNef k sX)
    (j : ℕ) : (j • D).IsNef k sX := by
  obtain ⟨hDc, hD⟩ := hD
  refine ⟨hDc.nsmul j, fun Cv i _ _ _ hC => ?_⟩
  rw [Divisor.degreeOn_nsmul' k sX i hC.le D hDc j]
  exact mul_nonneg (by positivity) (hD Cv i hC)

/-- **Ample plus nef is ample.** On a normal projective variety, the sum of an ample Cartier
divisor and a nef Cartier divisor is ample. -/
private theorem isAmple_add_of_isNef {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] [IsNormal X] [IsLocallyNoetherian X]
    [CompactSpace X] [QuasiCompact sX] {A N : Divisor X} (hA : A.IsCartier)
    (hAamp : A.IsAmple hA) (hN : N.IsNef k sX) : (A + N).IsAmple (hA.add hN.1) :=
  QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX
    ⟨1, one_pos, A, by rw [Nat.cast_one, one_smul], hA, hAamp⟩
    ((QDivisor.isNef_toQDivisor_iff N hN.1).mpr hN)
    (QDivisor.NumericallyEquivalent.refl
      ((QDivisor.isQCartier_toQDivisor hA).add (QDivisor.isQCartier_toQDivisor hN.1)))
    1 one_pos (A + N) (by rw [Nat.cast_one, one_smul, map_add]) _

/-- If `deg_C 𝒪_X(F) = n · deg_C 𝒪_X(D)` on every curve `C`, then `D ≡ (1/n) F`. -/
private theorem numericallyEquivalent_inv_smul_of_degreeOn_eq {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {D F : Divisor X} (hD : D.IsCartier) (hF : F.IsCartier) {n : ℕ} (hn : 0 < n)
    (hdeg : ∀ (C : Scheme.{0}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1),
      F.degreeOn k sX i hC.le hF = n * D.degreeOn k sX i hC.le hD) :
    (Divisor.toQDivisor D).NumericallyEquivalent k sX ((n : ℚ)⁻¹ • Divisor.toQDivisor F) := by
  have hnF : Divisor.toQDivisor F = (n : ℤ) • ((n : ℚ)⁻¹ • Divisor.toQDivisor F) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_inv_smul₀ (by positivity)]
  have hq : ((n : ℚ)⁻¹ • Divisor.toQDivisor F).IsQCartier := ⟨n, by omega, F, hnF, hF⟩
  refine ⟨QDivisor.isQCartier_toQDivisor hD, hq, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sX i hC.le D hD,
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq hn F hF hnF, hdeg C i hC]
  push_cast
  field_simp

end NefBig

/-- **Kollár–Mori 2.61 (1) ⇒ (3).** Let `X` be a normal projective variety over a field `k` and
`D` a nef (`Divisor.IsNef`) and big (`Divisor.IsBig`) Cartier divisor on `X`. Then there are an
effective Cartier divisor `E`, an integer `k₀ > 0` and ample `ℚ`-divisors `A n` with
`D ≡ A n + (1/n) E` for every `n ≥ k₀`. -/
@[mmp "lem_km2c_nef_big_ample_approximation"]
public theorem exists_numericallyEquivalent_isAmple_add_smul {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] (D : Divisor X) (hnef : D.IsNef k sX) (hbig : D.IsBig k sX) :
    ∃ (E : Divisor X) (k₀ : ℕ) (A : ℕ → QDivisor X), 0 ≤ E ∧ E.IsCartier ∧ 0 < k₀ ∧
      ∀ n : ℕ, k₀ ≤ n → (A n).IsAmple ∧
        (Divisor.toQDivisor D).NumericallyEquivalent k sX
          (A n + (n : ℚ)⁻¹ • Divisor.toQDivisor E) := by
  have hDc : D.IsCartier := hnef.1
  haveI := (IsProjectiveMorphism.isProjective
    (IsProjectiveVariety.isProjective (k := k) (f := sX))).isProper
  obtain ⟨m, hm, A, E, hAc, hAamp, hE, hEc, ⟨e⟩⟩ :=
    exists_iso_divisorialSheaf_ample_add_effective sX hDc hbig
  refine ⟨E, m, fun n => (n : ℚ)⁻¹ • Divisor.toQDivisor (A + (n - m) • D), hE, hEc, hm,
    fun n hn => ⟨⟨n, hm.trans_le hn, _,
      (smul_inv_smul₀ (by have := hm.trans_le hn; positivity) _).symm, _,
      isAmple_add_of_isNef sX hAc hAamp (isNef_nsmul sX hnef _)⟩, ?_⟩⟩
  rw [← smul_add, ← map_add]
  refine numericallyEquivalent_inv_smul_of_degreeOn_eq sX hDc ((hAc.add (hDc.nsmul _)).add hEc)
    (hm.trans_le hn) fun C i _ _ _ hC => ?_
  rw [Divisor.degreeOn_congr (add_right_comm A _ E) _ ((hAc.add hEc).add (hDc.nsmul _)),
    Divisor.degreeOn_add k sX i hC.le _ _ (hAc.add hEc) (hDc.nsmul _),
    ← degreeOn_eq_of_iso_divisorialSheaf sX i hC.le (hDc.nsmul m) _ e,
    Divisor.degreeOn_nsmul' k sX i hC.le D hDc, Divisor.degreeOn_nsmul' k sX i hC.le D hDc]
  push_cast [Nat.cast_sub hn]
  ring

end MMP.Mori
