module
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
/-!
# Intersections on threefolds and degrees on fibres of families of curves

Two results used in the analysis of flips on threefolds.

Let `X` be a normal projective threefold over a field `k` and `H` an ample `ℚ`-divisor on `X`.
If `G₁, G₂` are effective `ℚ`-Cartier divisors without common components, then
`G₁ · G₂ · H ≥ 0`, with equality exactly when `Supp G₁ ∩ Supp G₂ = ∅`. If `G` is an effective
`ℚ`-Cartier divisor and `N` a nef `ℚ`-Cartier divisor, then `G · N · H ≥ 0`. The intersection
number of `ℚ`-Cartier divisors `D₁, D₂, D₃` is computed by clearing denominators: if
`m_j D_j = E_j` with `m_j > 0` and `E_j` Cartier, then
`D₁ · D₂ · D₃ = (E₁ · E₂ · E₃ · X) / (m₁ m₂ m₃)`, where `(E₁ · E₂ · E₃ · X)` is
`MMP.Mori.Divisor.intersectionNumberOn`. The proof cuts `X` by the zero scheme of the canonical
section of `𝒪_X(E₁)` and reduces to surfaces and then to curves, on which an ample degree is
positive.

Let `π : G ⟶ Δ` be a proper flat morphism over a field `k`, where `Δ` is a connected smooth curve
over `k` or `Δ ≅ Spec k`, `G` is of finite type over `k`, and every fibre has dimension at most
one. For an invertible sheaf `L` on `G` and a closed point `t ∈ Δ`, the degree of `L` on the fibre
`G_t` is `deg_t L = ∑ᵢ mᵢ deg(νᵢ^* L)`, the sum over the one-dimensional irreducible components
`Cᵢ` of `G_t`, with `mᵢ` the length of `𝒪_{G_t}` at the generic point of `Cᵢ` and
`νᵢ : C̃ᵢ ⟶ Cᵢ` the normalization. Then `deg_t L = χ(G_t, L|_{G_t}) - χ(G_t, 𝒪_{G_t})`, and this
does not depend on `t`. Moreover (Hartshorne III.9.7), if `Δ` is a smooth curve, `Δ° ⊆ Δ` is a
dense open subset, `G₁` is proper over `Δ` and `G° ⊆ G₁` is an open subscheme lying over `Δ°` and
flat over it, then the scheme-theoretic closure of `G°` in `G₁` is proper and flat over `Δ`.

## Main results

* `MMP.Flips.intersectionNumberOn_nonneg_of_isEffective`: both assertions on threefolds, for
  every choice of Cartier multiples.
* `MMP.Flips.fibre_degree_eq_and_isProper_flat_closure`: the degree dictionary on fibres, its
  constancy, and flatness of the closure.

## Implementation notes

`X` is proper over `k` and carries an ample divisor, hence is projective. It is assumed normal,
the setting in which `MMP.Mori.Divisor` and the Cartier condition are defined, and integral, so
that every divisor of `X` lies on a component of dimension three. The statements are made for
every choice of positive multiples `m_j` and Cartier divisors `E_j = m_j D_j`; this choice also
witnesses that the `D_j` are `ℚ`-Cartier.

The fibre `G_t` is `π.fiber t`, a scheme over the residue field `κ(t)` through
`π.fiberToSpecResidueField t`, and degrees and Euler characteristics on it are taken over `κ(t)`.
The one-dimensional irreducible components of `G_t` are the proper curves `C` of `G_t`
(`MMP.Mori.ProperCurve`) whose closure is an irreducible component. A normalization of each is
any `ν : C̃ ⟶ C` with `MMP.Flips.IsCurveNormalization ν`; the identity holds for every such
choice. The difference `χ(G_t, L|_{G_t}) - χ(G_t, 𝒪_{G_t})` is
`AlgebraicGeometry.invertibleCurveDegree`. The scheme-theoretic closure of the open `U ⊆ G₁` is
the scheme-theoretic image of `U.ι`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], the proof of
  15.13
* [R. Hartshorne, *Algebraic geometry*, III.9.7]
-/

public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips

open MMP.Mori

private theorem prod_pos (m : Fin 3 → ℕ) (hm : ∀ j, 0 < m j) : 0 < ∏ j, (m j : ℚ) :=
  Finset.prod_pos fun j _ => by exact_mod_cast hm j

section Helpers

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A one-slot intersection number against a closed subscheme of dimension at most one is
nonnegative as soon as it is nonnegative on every integral curve. -/
private theorem intersectionNumber_one_nonneg_of_curves (f : X ⟶ Spec (.of k)) [IsProper f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ ((1 : ℕ) : WithBot ℕ∞))
    (A : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : ∀ (C : Scheme.{u}) (j : C ⟶ X) [IsClosedImmersion j] [IsIntegral C]
      (hC : topologicalKrullDim C = 1), 0 ≤ intersectionNumber k f j 1 hC.le fun _ => A) :
    0 ≤ intersectionNumber k f i 1 hd fun _ => A := by
  rw [intersectionNumber_eq_sum_dimComponents k f i 1 hd]
  refine finsum_nonneg fun W => mul_nonneg ?_ ?_
  · exact Int.natCast_nonneg _
  · have := W.2.1
    exact hA W.1.subscheme W.1.subschemeι (by exact_mod_cast W.2.2.2)

private instance isInvertible_vecCons2 (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] (t : Fin 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, B] t) := by
  fin_cases t <;> assumption

open Stacks.SheafOfModules.Invertible in
/-- Ample slot first: the intersection number `(B · A · W)` on an integral surface `W` is
nonnegative when `B` is ample and `A` is nonnegative on curves. -/
private theorem intersectionNumber_two_nonneg_of_curves (f : X ⟶ Spec (.of k)) [IsProper f]
    {W : Scheme.{u}} (j : W ⟶ X) [IsClosedImmersion j] [IsIntegral W]
    (hW : topologicalKrullDim W = 2) (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (hB : Scheme.Modules.IsAmple X B)
    (hA : ∀ (C : Scheme.{u}) (j : C ⟶ X) [IsClosedImmersion j] [IsIntegral C]
      (hC : topologicalKrullDim C = 1), 0 ≤ intersectionNumber k f j 1 hC.le fun _ => A) :
    0 ≤ intersectionNumber k f j 2 hW.le ![B, A] := by
  classical
  have hposdim : 0 < topologicalKrullDim W := by rw [hW]; exact_mod_cast Nat.succ_pos 1
  have hMinv : Stacks.Ample.IsInvertibleModule W
      ((Scheme.Modules.pullback j).obj B) := inferInstance
  have hMample : Scheme.Modules.IsAmple W ((Scheme.Modules.pullback j).obj B) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        j B (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X B hB)
        (Or.inl ⟨inferInstance, inferInstance⟩))
  obtain ⟨n, D, hn, hDcartier, hDne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k (j ≫ f) hposdim
      ((Scheme.Modules.pullback j).obj B) hMample
  set N : Fin 2 → X.Modules :=
    Function.update ![B, A] 0 (tensorPower X.presheaf X.ringCatSheaf.2 (![B, A] 0) (n : ℤ))
    with hN
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
    isInvertible_update ![B, A] 0 _
  have hNsucc : ∀ t : Fin 1, N t.succ = ![B, A] t.succ := fun t =>
    Function.update_of_ne (Fin.succ_ne_zero t) _ _
  have hNiso : (Scheme.Modules.pullback j).obj (N 0) ≅
      (Stacks.Divisors.invertibleSheaf D : W.Modules) := by
    refine Iso.trans ?_ e
    exact eqToIso (congrArg (Scheme.Modules.pullback j).obj
        (Function.update_self (0 : Fin 2) _ ![B, A])) ≪≫
      Scheme.Modules.pullbackTensorPowerIso j B n
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hDcartier
  have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor' k f j 1
    hW.le N D hNiso
  have hrec : 0 ≤ intersectionNumber k f (D.subschemeι ≫ j) 1
      (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f j 1 hW.le D)
      (fun t : Fin 1 => N t.succ) := by
    have hNsucc' : (fun t : Fin 1 => N t.succ) = fun _ : Fin 1 => A := funext fun t => by
      rw [hNsucc]
      obtain rfl : t = 0 := Subsingleton.elim _ _
      rfl
    have := intersectionNumber_one_nonneg_of_curves f (D.subschemeι ≫ j)
      (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f j 1 hW.le D)
      A hA
    simpa only [hNsucc'] using this
  have hmul := intersectionNumber_update_tensorPower k f j 2 hW.le ![B, A] 0 n
  have hprod : (0 : ℤ) ≤ (n : ℤ) * intersectionNumber k f j 2 hW.le ![B, A] := by
    rw [← hmul]
    exact hBEU ▸ hrec
  exact nonneg_of_mul_nonneg_right hprod (by exact_mod_cast hn)

/-- The swap of the two slots does not change a two-slot intersection number. -/
private theorem intersectionNumber_swap2 (f : X ⟶ Spec (.of k)) [IsProper f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hd : topologicalKrullDim Z ≤ ((2 : ℕ) : WithBot ℕ∞))
    (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    intersectionNumber k f i 2 hd ![A, B] = intersectionNumber k f i 2 hd ![B, A] := by
  have h := intersectionNumber_comp_perm k f i 2 hd ![B, A] (Equiv.swap 0 1)
  rw [← h]
  congr 1
  funext t
  fin_cases t <;> simp

/-- **Cut by an effective Cartier divisor, then nonnegativity on its surface components.**
On an integral threefold `X`, proper over `k`, if `L₀ ≅ 𝒪_X(Dv)` for an effective Cartier divisor
`Dv`, `L₂` is ample and `L₁` is nonnegative on curves, then `(L₀ · L₁ · L₂ · X) ≥ 0`. -/
private theorem intersectionNumber_three_nonneg_of_cut (f : X ⟶ Spec (.of k)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 3) (L : Fin 3 → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (Dv : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Dv]
    (hL₀ : (Scheme.Modules.pullback (𝟙 X)).obj (L 0) ≅ Stacks.Divisors.invertibleSheaf Dv)
    (hL₂ : Scheme.Modules.IsAmple X (L 2))
    (hL₁ : ∀ (C : Scheme.{u}) (j : C ⟶ X) [IsClosedImmersion j] [IsIntegral C]
      (hC : topologicalKrullDim C = 1), 0 ≤ intersectionNumber k f j 1 hC.le fun _ => L 1) :
    0 ≤ intersectionNumber k f (𝟙 X) 3 hd L := by
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 2 hd L Dv hL₀,
    intersectionNumber_eq_sum_dimComponents]
  refine finsum_nonneg fun W => mul_nonneg (Int.natCast_nonneg _) ?_
  haveI := W.2.1
  have hW := W.2.2.2
  have hfam : (fun t : Fin 2 => L t.succ) = ![L 1, L 2] := by
    funext t; fin_cases t <;> rfl
  rw [intersectionNumber_congr_family k f W.1.subschemeι 2 W.topologicalKrullDim_le hfam,
    intersectionNumber_swap2 f W.1.subschemeι W.topologicalKrullDim_le]
  exact intersectionNumber_two_nonneg_of_curves f W.1.subschemeι hW (L 1) (L 2) hL₂ hL₁

open Stacks.Ample Stacks.RelativeVeryAmple in
private noncomputable def tensorPowDivisorialIso [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (E : Divisor X) (hE : E.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] :
    (n : ℕ) → tensorPowModule X E.divisorialSheaf (n : ℤ) ≅ (n • E).divisorialSheaf
  | 0 => tensorPowModuleZeroIso X E.divisorialSheaf ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫
      eqToIso (by rw [zero_nsmul])
  | (n + 1) =>
      tensorPowModuleCongr X E.divisorialSheaf
          (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
        (tensorPowModuleAddIso X E.divisorialSheaf (n : ℤ) 1).symm ≪≫
        tensorModulesMapIso X (tensorPowDivisorialIso E hE n)
          (tensorPowModuleOneIso X E.divisorialSheaf) ≪≫
        (hE.nsmul n).divisorialSheafTensorIso hE ≪≫
        eqToIso (by rw [succ_nsmul])

open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmplePositivePower in
private theorem isAmple_divisorialSheaf_of_nsmul_eq [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (E D : Divisor X) (hE : E.IsCartier) (hD : D.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] [IsInvertibleModule X D.divisorialSheaf]
    (hDa : Stacks.Ample.IsAmple X D.divisorialSheaf) {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (h : m • E = m' • D) : Stacks.Ample.IsAmple X E.divisorialSheaf := by
  have h1 : Stacks.Ample.IsAmple X (tensorPowModule X D.divisorialSheaf (m' : ℤ)) :=
    isAmple_tensorPowModule_of_isAmple _ m' hm' hDa
  have e : tensorPowModule X D.divisorialSheaf (m' : ℤ) ≅
      tensorPowModule X E.divisorialSheaf (m : ℤ) :=
    tensorPowDivisorialIso D hD m' ≪≫ eqToIso (by rw [← h]) ≪≫
      (tensorPowDivisorialIso E hE m).symm
  exact isAmple_of_isAmple_tensorPowModule _ m hm
    ((isAmple_congr _ _ e).1 h1)

/-- The sheaf of a Cartier multiple of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_divisorialSheaf_of_isAmple [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) (E : Divisor X) (hE : E.IsCartier) {m₂ : ℕ}
    (hm₂ : 0 < m₂) (h : Divisor.toQDivisor E = (m₂ : ℚ) • H) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Scheme.Modules.IsAmple X E.divisorialSheaf := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hH
  haveI := hE.isInvertibleModule_divisorialSheaf
  haveI := hDc.isInvertibleModule_divisorialSheaf
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple X _).1 ?_
  refine isAmple_divisorialSheaf_of_nsmul_eq E D hE hDc hDa hm hm₂ ?_
  apply Divisor.toQDivisor_injective
  rw [map_nsmul, map_nsmul, h, hD, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, smul_smul, mul_comm]

/-- A Cartier multiple of a nef `ℚ`-divisor has nonnegative degree on every integral curve. -/
private theorem intersectionNumber_one_nonneg_of_isNef (sX : X ⟶ Spec (.of k)) [IsProper sX]
    [IsLocallyNoetherian X] [IsNormal X] {N : QDivisor X} (hN : N.IsNef k sX) (E : Divisor X)
    (hE : E.IsCartier) {m : ℕ} (hm : 0 < m) (h : Divisor.toQDivisor E = (m : ℚ) • N)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E.divisorialSheaf]
    (C : Scheme.{u}) (j : C ⟶ X) [IsClosedImmersion j] [IsIntegral C]
    (hC : topologicalKrullDim C = 1) :
    0 ≤ intersectionNumber k sX j 1 hC.le fun _ => E.divisorialSheaf := by
  obtain ⟨hQ, hcurve⟩ := hN
  have h1 := hcurve C j hC
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX j hC.le
    (Divisor.degreeOn_add k sX j hC.le) N hQ hm E hE
    (by rw [h, ← Int.cast_smul_eq_zsmul ℚ]; simp)] at h1
  have h2 : (0 : ℚ) ≤ (E.degreeOn k sX j hC.le hE : ℚ) := by
    simpa using (le_div_iff₀ (by exact_mod_cast hm : (0 : ℚ) < m)).1 h1
  rw [intersectionNumber_one_eq_invertibleCurveDegree]
  exact_mod_cast h2

open Opposite in
/-- The zero scheme of a nonzero global section of an invertible module on an integral scheme is
an effective Cartier divisor whose sheaf is the pullback along the identity. -/
private theorem cut_of_ne_zero [IsIntegral X] (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] (s : M.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X M (s.eval (op ⊤))) ∧
      Nonempty ((Scheme.Modules.pullback (𝟙 X)).obj M ≅
        Stacks.Divisors.invertibleSheaf (zeroScheme X M (s.eval (op ⊤)))) := by
  have hreg := isRegularSection_of_eval_top_ne_zero M s hs
  refine ⟨(isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X M s).2 hreg, ?_⟩
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X M s hreg).exists
  exact ⟨((Scheme.Modules.pullbackId X).app M) ≪≫ e.symm⟩

/-- An integral divisor with `ℚ`-multiple of an effective `ℚ`-divisor is effective. -/
private theorem nonneg_of_toQDivisor_eq {G : QDivisor X} (hG : G.IsEffective) (E : Divisor X)
    {m : ℕ} (hm : 0 < m) (h : Divisor.toQDivisor E = (m : ℚ) • G) : 0 ≤ E := by
  rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
  intro P
  have h1 := congrArg (fun D => D.coeff P) h
  simp only [Divisor.coeff_toQDivisor] at h1
  have h2 : (0 : ℚ) ≤ (E.coeff P : ℚ) := by
    rw [h1]
    exact mul_nonneg (by exact_mod_cast hm.le) (hG P)
  exact_mod_cast h2

open Opposite in
/-- The canonical section `1` of `𝒪_X(E)` of an effective divisor on an integral scheme is
nonzero. -/
private theorem eval_oneSection_ne_zero [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (E : Divisor X) (hE0 : 0 ≤ E) : (Divisor.divisorialSheafOneSection hE0).eval (op ⊤) ≠ 0 := by
  intro h
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  have h1 := congrArg (fun m : Γ(E.divisorialSheaf, ⊤) =>
      m.1 (⟨Z, trivial⟩ :
        {Z : irreducibleComponents X // componentGenericPoint X Z ∈ (⊤ : X.Opens)})) h
  change (1 : X.presheaf.stalk (componentGenericPoint X Z)) = 0 at h1
  exact one_ne_zero h1

open Opposite in
/-- Cutting an integral scheme by the pull-back of a global section of an invertible module that
does not vanish identically. -/
private theorem cut_pullback_section {C : Scheme.{u}} (j : C ⟶ X) [IsIntegral C] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (σ : Γ(M, ⊤))
    (hc : ∃ c : C, j c ∈ Stacks.Ample.nonvanishingLocus M σ) :
    ∃ (D : C.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D),
      Nonempty ((Scheme.Modules.pullback j).obj M ≅ Stacks.Divisors.invertibleSheaf D) ∧
      D.supportSet = (j ⁻¹' Stacks.Ample.nonvanishingLocus M σ)ᶜ := by
  have hs := MMP.Threefold.Mori.eval_pullbackSection_ne_zero j M σ hc
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv C ((Scheme.Modules.pullback j).obj M)).symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection j M σ)
  have hinv0 : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback j).obj M) := inferInstance
  have hinv : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback j).obj M) := hinv0
  have hreg := isRegularSection_of_eval_top_ne_zero _ s hs
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme C _ s hreg).exists
  refine ⟨zeroScheme C _ (s.eval (op ⊤)),
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection C _ s).2 hreg, ⟨e.symm⟩, ?_⟩
  have h := nonvanishingLocus_eq_compl_supportSet_zeroScheme _ s hs
  rw [MMP.Threefold.Mori.nonvanishingLocus_pullbackSection] at h
  rw [← compl_compl (zeroScheme C _ (s.eval (op ⊤))).supportSet, ← h]

/-- **One surface component.** For an integral surface `W` of `X` on which the section `σ` of
`M₁` does not vanish identically, `(M₁ · M₂ · W)` is nonnegative for ample `M₂`, and vanishes
exactly when `σ` has no zero on `W`. -/
private theorem surface_term (f : X ⟶ Spec (.of k)) [IsProper f] {W : Scheme.{u}} (j : W ⟶ X)
    [IsClosedImmersion j] [IsIntegral W] (hW : topologicalKrullDim W = 2) (M₁ M₂ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M₂]
    (hM₂ : Scheme.Modules.IsAmple X M₂) (σ : Γ(M₁, ⊤))
    (hc : ∃ c : W, j c ∈ Stacks.Ample.nonvanishingLocus M₁ σ) :
    0 ≤ intersectionNumber k f j 2 hW.le ![M₁, M₂] ∧
      (intersectionNumber k f j 2 hW.le ![M₁, M₂] = 0 ↔
        ∀ c : W, j c ∈ Stacks.Ample.nonvanishingLocus M₁ σ) := by
  obtain ⟨D, hD, ⟨e⟩, hsupp⟩ := cut_pullback_section j M₁ σ hc
  have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor' k f j 1 hW.le ![M₁, M₂] D e
  have hfam : (fun t : Fin 1 => (![M₁, M₂] : Fin 2 → X.Modules) t.succ) = fun _ => M₂ :=
    funext fun t => by
      obtain rfl : t = 0 := Subsingleton.elim _ _
      rfl
  have hmem : ∀ z : D.subscheme, ¬ j (D.subschemeι z) ∈ Stacks.Ample.nonvanishingLocus M₁ σ := by
    intro z hz
    have : D.subschemeι z ∈ D.supportSet := by
      change D.subschemeι z ∈ (D.support : Set W)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rw [hsupp] at this
    exact this hz
  have hmem' : ∀ c : W, j c ∉ Stacks.Ample.nonvanishingLocus M₁ σ → Nonempty D.subscheme := by
    intro c hcn
    have : c ∈ D.supportSet := by rwa [hsupp]
    change c ∈ (D.support : Set W) at this
    rw [← Scheme.IdealSheafData.range_subschemeι] at this
    obtain ⟨z, -⟩ := this
    exact ⟨z⟩
  have hBEU' : intersectionNumber k f j 2 hW.le ![M₁, M₂] =
      intersectionNumber k f (D.subschemeι ≫ j) 1
        (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f j 1
          hW.le D) (fun _ => M₂) :=
    hBEU.trans (intersectionNumber_congr_family k f _ 1 _ hfam)
  rw [hBEU']
  by_cases hne : Nonempty D.subscheme
  · have hdimD : topologicalKrullDim D.subscheme = ((1 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (j ≫ f) D hD
        (d := 1) (by rw [hW]; rfl)
    have hpos := intersectionNumber_pos k f (D.subschemeι ≫ j) 1 hdimD (fun _ => M₂)
      (fun _ => hM₂)
    obtain ⟨z⟩ := hne
    exact ⟨hpos.le, fun h0 => absurd h0 hpos.ne', fun hall => absurd (hall _) (hmem z)⟩
  · have hlt : topologicalKrullDim D.subscheme < ((1 : ℕ) : WithBot ℕ∞) := by
      rw [(topologicalKrullDim_eq_bot_iff_isEmpty D.subscheme).2 (not_nonempty_iff.1 hne)]
      exact WithBot.bot_lt_coe _
    have h0 := intersectionNumber_eq_zero_of_topologicalKrullDim_lt k f (D.subschemeι ≫ j) 1 hlt.le
      hlt (fun _ => M₂)
    rw [h0]
    exact ⟨le_rfl, fun _ c => not_not.1 fun hcn => hne (hmem' c hcn), fun _ => rfl⟩

/-- The multiplicity at the generic point of a `d`-dimensional integral component of a closed
subscheme of dimension at most `d` is positive. -/
private theorem sheafMultiplicity_genericPt_pos' (f : X ⟶ Spec (.of k)) [IsProper f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))
    (W : DimIntegralSubscheme ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) d) :
    0 < Stacks.Chow.sheafMultiplicity
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) W.genericPt := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hZcoh : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  have hFcoh : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i (Stacks.Ample.unitModule Z)
  have hdimF : topologicalKrullDim (_root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) =
      (d : WithBot ℕ∞) := by
    rw [Stacks.Chow.supp_pushforwardStructureSheaf i, topologicalKrullDim_range_eq i]
    refine le_antisymm hd ?_
    rw [← W.2.2.2, ← topologicalKrullDim_support_eq W.1]
    calc topologicalKrullDim (W.1.support : Set X)
        ≤ topologicalKrullDim (_root_.SheafOfModules.supp
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) :=
          (Topology.IsEmbedding.inclusion W.2.2.1).isInducing.topologicalKrullDim_le
      _ = topologicalKrullDim (Set.range i) := by
          rw [Stacks.Chow.supp_pushforwardStructureSheaf i]
      _ = topologicalKrullDim Z := topologicalKrullDim_range_eq i
  exact sheafMultiplicity_genericPt_pos k f _
    (⟨W.1, W.2.1, W.2.2.1, by rw [hdimF]; exact W.2.2.2⟩ : TopDimIntegralSubscheme _)

/-- The structure sheaf of a closed subscheme, as a module on the ambient scheme. -/
private noncomputable abbrev cutModule (D : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward (D.subschemeι ≫ 𝟙 X)).obj (Stacks.Ample.unitModule D.subscheme)

/-- **Cutting a threefold by the first module.** If `σ` is a global section of `L₀` which does not
vanish identically on an integral `X`, then `(L₀ · L₁ · L₂ · X)` is the weighted sum of the
`(L₁ · L₂ · W)` over the integral surfaces `W` of the zero scheme `D` of `σ`, with positive
weights. -/
private theorem top_cut (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hd : topologicalKrullDim X ≤ ((2 + 1 : ℕ) : WithBot ℕ∞)) (L : Fin 3 → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)] (σ : Γ(L 0, ⊤))
    (hc : ∃ c : X, c ∈ Stacks.Ample.nonvanishingLocus (L 0) σ) :
    ∃ (D : X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D),
      D.supportSet = (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ ∧
      Finite (DimIntegralSubscheme (cutModule D) 2) ∧
      (∀ W : DimIntegralSubscheme (cutModule D) 2,
        0 < Stacks.Chow.sheafMultiplicity (cutModule D) W.genericPt) ∧
      intersectionNumber k f (𝟙 X) 3 hd L =
        ∑ᶠ W : DimIntegralSubscheme (cutModule D) 2,
          Stacks.Chow.sheafMultiplicity (cutModule D) W.genericPt *
            intersectionNumber k f W.1.subschemeι 2 W.topologicalKrullDim_le
              (fun t : Fin 2 => L t.succ) := by
  obtain ⟨D, hD, ⟨e⟩, hsupp⟩ := cut_pullback_section (𝟙 X) (L 0) σ (by simpa using hc)
  have hD2 : topologicalKrullDim D.subscheme ≤ ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f (𝟙 X) 2 hd D
  refine ⟨D, hD, by simpa using hsupp, finite_dimIntegralSubscheme k f _ 2 hD2,
    fun W => sheafMultiplicity_genericPt_pos' f _ 2 hD2 W, ?_⟩
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 2 hd L D e,
    intersectionNumber_eq_sum_dimComponents]

private theorem supp_cutModule (D : X.IdealSheafData) :
    SheafOfModules.supp (cutModule D) = D.supportSet := by
  rw [cutModule, Stacks.Chow.supp_pushforwardStructureSheaf, Category.comp_id,
    Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The three consequences of `top_cut` used for threefolds: nonnegativity, vanishing and
positivity of `(L₀ · L₁ · L₂ · X)` from the behaviour of the surface components. -/
private theorem top_cut_sign (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hd : topologicalKrullDim X ≤ ((2 + 1 : ℕ) : WithBot ℕ∞)) (L : Fin 3 → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)] (σ : Γ(L 0, ⊤))
    (hc : ∃ c : X, c ∈ Stacks.Ample.nonvanishingLocus (L 0) σ) :
    ((∀ (W : X.IdealSheafData) (_ : IsIntegral W.subscheme)
        (hW : topologicalKrullDim W.subscheme = 2),
        (W.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ →
          0 ≤ intersectionNumber k f W.subschemeι 2 hW.le (fun t : Fin 2 => L t.succ)) →
      0 ≤ intersectionNumber k f (𝟙 X) 3 hd L) ∧
    ((∀ (W : X.IdealSheafData) (_ : IsIntegral W.subscheme)
        (hW : topologicalKrullDim W.subscheme = 2),
        (W.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ →
          intersectionNumber k f W.subschemeι 2 hW.le (fun t : Fin 2 => L t.succ) = 0) →
      intersectionNumber k f (𝟙 X) 3 hd L = 0) ∧
    ((∀ (W : X.IdealSheafData) (_ : IsIntegral W.subscheme)
        (hW : topologicalKrullDim W.subscheme = 2),
        (W.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ →
          0 ≤ intersectionNumber k f W.subschemeι 2 hW.le (fun t : Fin 2 => L t.succ)) →
      ∀ (W₀ : X.IdealSheafData) (_ : IsIntegral W₀.subscheme)
        (hW₀ : topologicalKrullDim W₀.subscheme = 2),
        (W₀.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ →
        0 < intersectionNumber k f W₀.subschemeι 2 hW₀.le (fun t : Fin 2 => L t.succ) →
      0 < intersectionNumber k f (𝟙 X) 3 hd L) := by
  obtain ⟨D, hD, hsupp, hfin, hmult, hN⟩ := top_cut f hd L σ hc
  have hsub : ∀ W : DimIntegralSubscheme (cutModule D) 2,
      (W.1.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (L 0) σ)ᶜ := fun W =>
    (W.2.2.1.trans (supp_cutModule D).subset).trans hsupp.subset
  refine ⟨fun h => ?_, fun h => ?_, fun h W₀ hW₀i hW₀ hW₀s hW₀p => ?_⟩
  · rw [hN]
    exact finsum_nonneg fun W => mul_nonneg (hmult W).le
      (h W.1 W.2.1 W.2.2.2 (hsub W))
  · rw [hN]
    exact finsum_eq_zero_of_forall_eq_zero fun W => by
      rw [h W.1 W.2.1 W.2.2.2 (hsub W), mul_zero]
  · rw [hN]
    haveI : Fintype (DimIntegralSubscheme (cutModule D) 2) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    let W₀' : DimIntegralSubscheme (cutModule D) 2 :=
      ⟨W₀, hW₀i, (hW₀s.trans hsupp.symm.subset).trans (supp_cutModule D).symm.subset, hW₀⟩
    refine Finset.sum_pos' (fun W _ => mul_nonneg (hmult W).le
      (h W.1 W.2.1 W.2.2.2 (hsub W))) ⟨W₀', Finset.mem_univ _, mul_pos (hmult W₀') hW₀p⟩

open TopologicalSpace Order in
private theorem genericPoint_notMem_support [IsIntegral X] (P : MMP.Mori.PrimeDivisor X) :
    genericPoint X ∉ P.support := by
  intro h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hP := P.codimension_closure_genericPoint
  have huniv : closure ({P.genericPoint} : Set X) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    have : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
    rw [← this]
    exact closure_minimal (Set.singleton_subset_iff.2 h) isClosed_closure
  have hmax : IsMax (IrreducibleCloseds.closureSingleton P.genericPoint) := by
    intro b _
    change (b : Set X) ⊆ closure ({P.genericPoint} : Set X)
    rw [huniv]
    exact Set.subset_univ _
  rw [codimension_eq_coheight, Order.coheight_eq_zero.2 hmax] at hP
  exact zero_ne_one hP

open TopologicalSpace Order in
/-- A dimension-two integral closed subscheme of an integral threefold cannot lie on two distinct
prime divisors. -/
private theorem false_of_two_primeDivisors [IsIntegral X] (hX : topologicalKrullDim X = 3)
    (P Q : MMP.Mori.PrimeDivisor X) (hPQ : P ≠ Q) (W : X.IdealSheafData)
    (hWi : IsIntegral W.subscheme) (hW : topologicalKrullDim W.subscheme = 2)
    (hP : (W.support : Set X) ⊆ P.support) (hQ : (W.support : Set X) ⊆ Q.support) : False := by
  set A : IrreducibleCloseds X :=
    IrreducibleCloseds.closureSingleton (Stacks.Chow.genericPointOf W hWi) with hA
  have hAsupp : (A : Set X) = W.support := by
    rw [hA]
    exact (Stacks.Chow.support_eq_closure_genericPointOf W hWi).symm
  have hAh : Order.height A = 2 := by
    have h1 := topologicalKrullDim_irreducibleCloseds A
    rw [hAsupp, topologicalKrullDim_support_eq W, hW] at h1
    exact WithBot.coe_injective (h1.symm.trans (by norm_num))
  have key : ∀ R : MMP.Mori.PrimeDivisor X, (W.support : Set X) ⊆ R.support →
      A = IrreducibleCloseds.closureSingleton R.genericPoint := by
    intro R hR
    have hle : A ≤ IrreducibleCloseds.closureSingleton R.genericPoint := by
      change (A : Set X) ⊆ closure ({R.genericPoint} : Set X)
      rw [hAsupp, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hR
    refine hle.eq_or_lt.elim id fun hlt => ?_
    have hc := R.codimension_closure_genericPoint
    rw [codimension_eq_coheight] at hc
    haveI : Nonempty (IrreducibleCloseds X) := ⟨A⟩
    have h2 := coheight_add_one_le hlt
    rw [hc] at h2
    have h3 : (Order.height A + Order.coheight A : ℕ∞) ≤ 3 := by
      have h4 := krullDim_eq_iSup_height_add_coheight_of_nonempty (α := IrreducibleCloseds X)
      have h5 : (3 : WithBot ℕ∞) = krullDim (IrreducibleCloseds X) := hX.symm
      rw [h4] at h5
      have h6 : (Order.height A + Order.coheight A : ℕ∞) ≤
          ⨆ a : IrreducibleCloseds X, (Order.height a + Order.coheight a) :=
        le_iSup (fun a : IrreducibleCloseds X => Order.height a + Order.coheight a) A
      have : (⨆ a : IrreducibleCloseds X, (Order.height a + Order.coheight a)) = 3 :=
        WithBot.coe_injective (h5.symm.trans (by norm_num))
      rwa [this] at h6
    rw [hAh] at h3
    have h2' : (2 : ℕ∞) ≤ Order.coheight A := le_trans (by norm_num) h2
    have : (2 : ℕ∞) + 2 ≤ 3 := le_trans (add_le_add le_rfl h2') h3
    exact absurd this (by norm_num)
  have hPQ' := (key P hP).symm.trans (key Q hQ)
  have : P.genericPoint = Q.genericPoint := by
    have h1 := congrArg (fun a : IrreducibleCloseds X => (a : Set X)) hPQ'
    simp only [IrreducibleCloseds.coe_closureSingleton] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  exact hPQ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective this)

/-- A prime divisor of an integral threefold of finite type over `k` is a surface. -/
private theorem topologicalKrullDim_primeDivisor (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    [IsIntegral X] (hX : topologicalKrullDim X = 3) (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim P.idealSheaf.subscheme = 2 := by
  haveI := P.integral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField k P.idealSheaf.subscheme
    (P.idealSheaf.subschemeι ≫ g)]
  have hvalue (ξ : genericPoints P.idealSheaf.subscheme) :
      letI : Algebra k (P.idealSheaf.subscheme.residueField ξ.1) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (P.idealSheaf.subschemeι ≫ g).appTop ≫
          P.idealSheaf.subscheme.Γevaluation ξ.1).hom.toAlgebra
      (Cardinal.toENat (Algebra.trdeg k (P.idealSheaf.subscheme.residueField ξ.1)) :
        WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by
    letI : Algebra k (X.residueField (P.idealSheaf.subschemeι ξ.1)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫
        X.Γevaluation (P.idealSheaf.subschemeι ξ.1)).hom.toAlgebra
    letI : Algebra k (P.idealSheaf.subscheme.residueField ξ.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (P.idealSheaf.subschemeι ≫ g).appTop ≫
        P.idealSheaf.subscheme.Γevaluation ξ.1).hom.toAlgebra
    rw [← trdeg_residueField_of_surjectiveOnStalks k g P.idealSheaf.subschemeι ξ.1]
    have hξ : P.idealSheaf.subschemeι ξ.1 = P.genericPoint := by
      have h : ξ.1 ∈ ({genericPoint P.idealSheaf.subscheme} : Set P.idealSheaf.subscheme) := by
        rw [← genericPoints_eq_singleton]
        exact ξ.2
      rw [Set.mem_singleton_iff.1 h]
      rfl
    have hlocal : ringKrullDim (X.presheaf.stalk (P.idealSheaf.subschemeι ξ.1)) = 1 := by
      rw [hξ]
      exact AlgebraicGeometry.PrimeDivisor.ringKrullDim_stalk_genericPoint_eq_one P
    have hformula := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X g
      (P.idealSheaf.subschemeι ξ.1)
    rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X g
      (P.idealSheaf.subschemeι ξ.1), hX, hlocal] at hformula
    refine ENat.WithBot.add_one_cancel.mp (hformula.symm.trans ?_)
    norm_num
  simp_rw [hvalue]
  haveI : Nonempty (genericPoints P.idealSheaf.subscheme) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty P.idealSheaf.subscheme)
    exact ⟨genericPoints.ofComponent
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩
  simp

/-- The set-theoretic support of a `ℚ`-multiple. -/
private theorem supp_eq_of_toQDivisor_eq {G : QDivisor X} {E : Divisor X} {m : ℕ} (hm : 0 < m)
    (h : Divisor.toQDivisor E = (m : ℚ) • G) : (E.supp : Set X) = G.supp := by
  have hc : ∀ P, E.coeff P ≠ 0 ↔ G.coeff P ≠ 0 := by
    intro P
    have h1 := congrArg (fun D => D.coeff P) h
    simp only [Divisor.coeff_toQDivisor] at h1
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Int.cast_ne_zero (α := ℚ), h1]
    simp [DivisorWithCoeffs.coeff_smul, hm']
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff,
    DivisorWithCoeffs.mem_supp_iff]
  exact exists_congr fun P => and_congr_left fun _ => hc P

/-- The generic point of an integral surface lying on a component of `G₁` does not lie on `G₂`
when `G₁` and `G₂` have no common component. -/
private theorem genericPointOf_notMem_supp [IsIntegral X] (hX : topologicalKrullDim X = 3)
    {G₁ G₂ : QDivisor X} (h₁₂ : Disjoint G₁.support G₂.support) (W : X.IdealSheafData)
    (hWi : IsIntegral W.subscheme) (hW : topologicalKrullDim W.subscheme = 2)
    (hWG : (W.support : Set X) ⊆ G₁.supp) :
    Stacks.Chow.genericPointOf W hWi ∉ (G₂.supp : Set X) := by
  intro h2
  have hη : Stacks.Chow.genericPointOf W hWi ∈ (W.support : Set X) := by
    rw [Stacks.Chow.support_eq_closure_genericPointOf W hWi]
    exact subset_closure rfl
  obtain ⟨P, hP, hηP⟩ := DivisorWithCoeffs.mem_supp_iff.1 (hWG hη)
  obtain ⟨Q, hQ, hηQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 h2
  have hPQ : P ≠ Q := by
    rintro rfl
    exact Finset.disjoint_left.1 h₁₂ (Finsupp.mem_support_iff.2 hP) (Finsupp.mem_support_iff.2 hQ)
  have hsub : ∀ R : MMP.Mori.PrimeDivisor X, Stacks.Chow.genericPointOf W hWi ∈ R.support →
      (W.support : Set X) ⊆ R.support := fun R hR => by
    rw [Stacks.Chow.support_eq_closure_genericPointOf W hWi]
    exact closure_minimal (Set.singleton_subset_iff.2 hR) R.idealSheaf.support.isClosed
  exact false_of_two_primeDivisors hX P Q hPQ W hWi hW (hsub P hηP) (hsub Q hηQ)

end Helpers

/-- **One surface component of `E₀`.** On an integral surface `W` contained in `Supp G₁`, the
intersection number `(E₁ · E₂ · W)` is nonnegative, and vanishes exactly when `W` misses
`Supp E₁`. -/
private theorem surface_term_oneSection (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : topologicalKrullDim X = 3) {G₁ G₂ : QDivisor X} (h₁₂ : Disjoint G₁.support G₂.support)
    (E : Fin 3 → Divisor X) (hE : ∀ j, (E j).IsCartier)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E j).divisorialSheaf]
    (hE0 : 0 ≤ E 0) (hE1 : 0 ≤ E 1) (hS0 : ((E 0).supp : Set X) = G₁.supp)
    (hS1 : ((E 1).supp : Set X) = G₂.supp) (hamp : Scheme.Modules.IsAmple X (E 2).divisorialSheaf)
    (W : X.IdealSheafData) (hWi : IsIntegral W.subscheme)
    (hW2 : topologicalKrullDim W.subscheme = 2)
    (hWs : (W.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus (E 0).divisorialSheaf
      (MMP.Threefold.Mori.oneSection hE0))ᶜ) :
    0 ≤ intersectionNumber k sX W.subschemeι 2 hW2.le
        (fun t : Fin 2 => (fun j => (E j).divisorialSheaf) t.succ) ∧
      (intersectionNumber k sX W.subschemeι 2 hW2.le
        (fun t : Fin 2 => (fun j => (E j).divisorialSheaf) t.succ) = 0 ↔
        ∀ c : W.subscheme, W.subschemeι c ∈ ((E 1).supp : Set X)ᶜ) := by
  have hn1 := MMP.Threefold.Mori.nonvanishingLocus_oneSection hE1 (hE 1)
  rw [MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 (hE 0), compl_compl, hS0] at hWs
  have hgen := genericPointOf_notMem_supp hX h₁₂ W hWi hW2 hWs
  have hη : Stacks.Chow.genericPointOf W hWi ∈ (W.support : Set X) := by
    rw [Stacks.Chow.support_eq_closure_genericPointOf W hWi]
    exact subset_closure rfl
  rw [← Scheme.IdealSheafData.range_subschemeι] at hη
  obtain ⟨c, hc⟩ := hη
  have hfam : (fun t : Fin 2 => (fun j => (E j).divisorialSheaf) t.succ) =
      ![(E 1).divisorialSheaf, (E 2).divisorialSheaf] := by
    funext t
    fin_cases t <;> rfl
  rw [intersectionNumber_congr_family k sX W.subschemeι 2 hW2.le hfam, ← hn1]
  exact surface_term (k := k) sX W.subschemeι hW2 (E 1).divisorialSheaf
    (E 2).divisorialSheaf hamp (MMP.Threefold.Mori.oneSection hE1) ⟨c, by rwa [hn1, hc, hS1]⟩

/-- Integral form of part 1: the integral intersection number of the Cartier multiples. -/
private theorem intersectionNumberOn_nonneg_and_eq_zero_iff (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : topologicalKrullDim X = 3) {H : QDivisor X}
    (hH : haveI := QuasiCompact.compactSpace_of_compactSpace sX; H.IsAmple)
    (G₁ G₂ : QDivisor X) (h₁ : G₁.IsEffective) (h₂ : G₂.IsEffective)
    (h₁₂ : Disjoint G₁.support G₂.support)
    (E : Fin 3 → Divisor X) (hE : ∀ j, (E j).IsCartier) (m : Fin 3 → ℕ) (hm : ∀ j, 0 < m j)
    (hEG : ∀ j, Divisor.toQDivisor (E j) = (m j : ℚ) • ![G₁, G₂, H] j) :
    0 ≤ Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE ∧
      (Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE = 0 ↔
        Disjoint (G₁.supp : Set X) G₂.supp) := by
  classical
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI hinv : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (E j).divisorialSheaf := fun j => (hE j).isInvertibleModule_divisorialSheaf
  have hE0 : 0 ≤ E 0 := nonneg_of_toQDivisor_eq h₁ (E 0) (hm 0) (by simpa using hEG 0)
  have hS0 : ((E 0).supp : Set X) = G₁.supp :=
    supp_eq_of_toQDivisor_eq (hm 0) (by simpa using hEG 0)
  have hS1 : ((E 1).supp : Set X) = G₂.supp :=
    supp_eq_of_toQDivisor_eq (hm 1) (by simpa using hEG 1)
  have hW := surface_term_oneSection k sX hX h₁₂ E hE hE0
    (nonneg_of_toQDivisor_eq h₂ (E 1) (hm 1) (by simpa using hEG 1)) hS0 hS1
    (isAmple_divisorialSheaf_of_isAmple hH (E 2) (hE 2) (hm 2) (by simpa using hEG 2))
  have hn0 := MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 (hE 0)
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  obtain ⟨hA, hB, hC⟩ := top_cut_sign sX hX.le (fun j => (E j).divisorialSheaf)
    (MMP.Threefold.Mori.oneSection hE0) ⟨genericPoint X, by
      rw [hn0]
      intro hmem
      obtain ⟨P, -, hP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
      exact genericPoint_notMem_support P hP⟩
  refine ⟨hA fun W hWi hW2 hWs => (hW W hWi hW2 hWs).1, fun hN => ?_,
    fun hd => hB fun W hWi hW2 hWs => ?_⟩
  · by_contra hnd
    obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.1 hnd
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.1 hx1
    have hPs : (P.idealSheaf.support : Set X) ⊆ (Stacks.Ample.nonvanishingLocus
        (E 0).divisorialSheaf (MMP.Threefold.Mori.oneSection hE0))ᶜ := by
      rw [hn0, compl_compl, hS0]
      exact DivisorWithCoeffs.support_subset_supp hP
    have hdim := topologicalKrullDim_primeDivisor sX hX P
    obtain ⟨hnn, hiff⟩ := hW P.idealSheaf P.integral hdim hPs
    have hne : intersectionNumber k sX P.idealSheaf.subschemeι 2 hdim.le
        (fun t : Fin 2 => (fun j => (E j).divisorialSheaf) t.succ) ≠ 0 := by
      intro h0
      obtain ⟨c, rfl⟩ : x ∈ Set.range P.idealSheaf.subschemeι := by
        rwa [Scheme.IdealSheafData.range_subschemeι]
      exact hiff.1 h0 c (by rwa [hS1])
    exact (hC (fun W hWi hW2 hWs => (hW W hWi hW2 hWs).1) P.idealSheaf P.integral hdim hPs
      (hnn.lt_of_ne' hne)).ne' hN
  · refine (hW W hWi hW2 hWs).2.2 fun c hmem => ?_
    have h2 := hWs (by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨c, rfl⟩ : W.subschemeι c ∈ (W.support : Set X))
    rw [hn0, compl_compl, hS0] at h2
    rw [hS1] at hmem
    exact Set.disjoint_left.1 hd h2 hmem

/-- Integral form of part 2. -/
private theorem intersectionNumberOn_nonneg_of_isNef (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : topologicalKrullDim X = 3) {H : QDivisor X}
    (hH : haveI := QuasiCompact.compactSpace_of_compactSpace sX; H.IsAmple)
    (G N : QDivisor X) (hG : G.IsEffective) (hN : N.IsNef k sX)
    (E : Fin 3 → Divisor X) (hE : ∀ j, (E j).IsCartier) (m : Fin 3 → ℕ) (hm : ∀ j, 0 < m j)
    (hEG : ∀ j, Divisor.toQDivisor (E j) = (m j : ℚ) • ![G, N, H] j) :
    0 ≤ Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI hinv : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (E j).divisorialSheaf := fun j => (hE j).isInvertibleModule_divisorialSheaf
  have hE0 : 0 ≤ E 0 := nonneg_of_toQDivisor_eq hG (E 0) (hm 0) (by simpa using hEG 0)
  haveI : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (E 0).divisorialSheaf := hinv 0
  obtain ⟨hcart, ⟨hiso⟩⟩ := cut_of_ne_zero (E 0).divisorialSheaf
    (Divisor.divisorialSheafOneSection hE0) (eval_oneSection_ne_zero (E 0) hE0)
  have hamp := isAmple_divisorialSheaf_of_isAmple hH (E 2) (hE 2) (hm 2) (by simpa using hEG 2)
  have hnef := intersectionNumber_one_nonneg_of_isNef sX hN (E 1) (hE 1) (hm 1)
    (by simpa using hEG 1)
  unfold Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_three_nonneg_of_cut sX hX.le (fun j => (E j).divisorialSheaf)
    _ hiso hamp hnef

/-- **Effective divisors meet an ample divisor nonnegatively on a threefold.** Let `X` be a normal
integral threefold, proper over a field `k`, and `H` an ample `ℚ`-divisor on `X`. For Cartier
divisors `E_j` and positive integers `m_j` with `E_j = m_j D_j` (`j = 0, 1, 2`, `D₂ = H`), write
`D₀ · D₁ · H = (E₀ · E₁ · E₂ · X) / (m₀ m₁ m₂)`.
1. If `D₀ = G₁` and `D₁ = G₂` are effective without common components, then `G₁ · G₂ · H ≥ 0`,
   and `G₁ · G₂ · H = 0` if and only if `Supp G₁` and `Supp G₂` are disjoint.
2. If `D₀ = G` is effective and `D₁ = N` is nef, then `G · N · H ≥ 0`. -/
@[mmp "lem_mmp_fa15_effective_threefold_intersections"]
public theorem intersectionNumberOn_nonneg_of_isEffective (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : topologicalKrullDim X = 3) {H : QDivisor X}
    (hH : haveI := QuasiCompact.compactSpace_of_compactSpace sX; H.IsAmple) :
    (∀ (G₁ G₂ : QDivisor X), G₁.IsEffective → G₂.IsEffective → Disjoint G₁.support G₂.support →
      ∀ (E : Fin 3 → Divisor X) (hE : ∀ j, (E j).IsCartier) (m : Fin 3 → ℕ), (∀ j, 0 < m j) →
        (∀ j, Divisor.toQDivisor (E j) = (m j : ℚ) • ![G₁, G₂, H] j) →
        0 ≤ (Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE : ℚ) / ∏ j, (m j : ℚ) ∧
          ((Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE : ℚ) / ∏ j, (m j : ℚ) = 0 ↔
            Disjoint (G₁.supp : Set X) G₂.supp)) ∧
    (∀ (G N : QDivisor X), G.IsEffective → N.IsNef k sX →
      ∀ (E : Fin 3 → Divisor X) (hE : ∀ j, (E j).IsCartier) (m : Fin 3 → ℕ), (∀ j, 0 < m j) →
        (∀ j, Divisor.toQDivisor (E j) = (m j : ℚ) • ![G, N, H] j) →
        0 ≤ (Divisor.intersectionNumberOn k sX (𝟙 X) 3 hX.le E hE : ℚ) / ∏ j, (m j : ℚ)) := by
  refine ⟨fun G₁ G₂ h₁ h₂ h₁₂ E hE m hm hEG => ?_, fun G N hG hN E hE m hm hEG => ?_⟩
  · obtain ⟨hnn, heq⟩ := intersectionNumberOn_nonneg_and_eq_zero_iff k sX hX hH G₁ G₂ h₁ h₂ h₁₂
      E hE m hm hEG
    refine ⟨div_nonneg (by exact_mod_cast hnn) (prod_pos m hm).le, ?_⟩
    rw [div_eq_zero_iff, or_iff_left (prod_pos m hm).ne', ← heq]
    exact_mod_cast Iff.rfl
  · exact div_nonneg
      (by exact_mod_cast intersectionNumberOn_nonneg_of_isNef k sX hX hH G N hG hN E hE m hm hEG)
      (prod_pos m hm).le

open TopologicalSpace

section helpers

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}

private theorem not_const_of_isCurveNormalization (C : Mori.ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

private theorem isCurve_comp (C : Mori.ProperCurve sX) {C' : Scheme} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) := ⟨⟩
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

private theorem degreeOn_normalization (C : Mori.ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    Mori.degreeOn k sX (ν ≫ C.ι) hdim M = Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [Mori.degreeOn, Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

end helpers

section dimComponents

variable {X : Scheme.{u}}

private theorem eq_vanishingIdeal_closure_genericPt (Z : X.IdealSheafData)
    [IsIntegral Z.subscheme] :
    Z = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({Z.subschemeι (genericPoint Z.subscheme)} : Set X)) := by
  have hc : Closeds.closure ({Z.subschemeι (genericPoint Z.subscheme)} : Set X) = Z.support :=
    Closeds.ext (Stacks.Chow.support_eq_closure_genericPointOf Z ‹_›).symm
  rw [hc]
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme Z Z.support rfl

private theorem false_of_specializes_of_topologicalKrullDim_le_one
    (hX : topologicalKrullDim X ≤ 1) {a b c : X} (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) : False := by
  have h := two_le_topologicalKrullDim_of_specializes (S := (Set.univ : Set X))
    (Set.mem_univ a) (Set.mem_univ b) (Set.mem_univ c) hab hbc hab' hbc'
  have := (h.trans (topologicalKrullDim_subspace_le X Set.univ)).trans hX
  exact absurd this (by norm_num)

private theorem exists_ne_genericPoint {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : topologicalKrullDim Z = 1) : ∃ z : Z, z ≠ genericPoint Z := by
  by_contra! h
  have : Subsingleton Z := ⟨fun a b => (h a).trans (h b).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology Z
  rw [hZ] at h0
  exact absurd h0 (by decide)

private theorem closure_genericPt_mem_irreducibleComponents (hX : topologicalKrullDim X ≤ 1)
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme] (hZ : topologicalKrullDim Z.subscheme = 1) :
    closure {Z.subschemeι (genericPoint Z.subscheme)} ∈ irreducibleComponents X := by
  obtain ⟨z, hz⟩ := exists_ne_genericPoint hZ
  set p := Z.subschemeι (genericPoint Z.subscheme)
  have hpq : p ⤳ Z.subschemeι z := ((genericPoint_specializes z).map Z.subschemeι.continuous)
  have hpq' : p ≠ Z.subschemeι z := fun h =>
    hz (Z.subschemeι.isClosedEmbedding.injective h).symm
  refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
  have hgen := hT.isGenericPoint_genericPoint_closure
  set t := hT.genericPoint
  have hpt : p ∈ closure T := subset_closure (hle (subset_closure rfl))
  have htp : t ⤳ p := by
    rw [specializes_iff_mem_closure, hgen.def]; exact hpt
  by_cases h : t = p
  · rw [h] at hgen
    intro x hx
    have := subset_closure hx
    rw [← hgen.def] at this
    exact this
  · exact (false_of_specializes_of_topologicalKrullDim_le_one hX htp hpq h hpq').elim

private noncomputable abbrev unitPushforward (X : Scheme.{u}) : X.Modules :=
  (Scheme.Modules.pushforward (𝟙 X)).obj (Stacks.Ample.unitModule X)

private theorem supp_unitPushforward : SheafOfModules.supp (unitPushforward X) = Set.univ := by
  rw [unitPushforward, Stacks.Chow.supp_pushforwardStructureSheaf]
  simp

private theorem sheafMultiplicity_unitPushforward (x : X) :
    Stacks.Chow.sheafMultiplicity (unitPushforward X) x =
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  have h := Stacks.Chow.length_stalk_pushforwardStructureSheaf (𝟙 X) x
    (Topology.IsInducing.id)
  unfold Stacks.Chow.sheafMultiplicity
  rw [Scheme.Hom.stalkMap_id] at h
  congr 2

section toW

variable {K : Type u} [Field K] (sX : X ⟶ Spec (.of K))

private noncomputable def toW (C : Mori.ProperCurve sX) :
    DimIntegralSubscheme (unitPushforward X) 1 :=
  ⟨Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X)),
    Mori.ProperCurve.isIntegral_scheme C,
    by rw [supp_unitPushforward]; exact Set.subset_univ _,
    by simpa using C.dim_eq⟩

private theorem genericPt_toW (C : Mori.ProperCurve sX) : (toW sX C).genericPt = C.point := by
  have h1 := Stacks.Chow.support_eq_closure_genericPointOf (toW sX C).1 (toW sX C).2.1
  have h2 : ((toW sX C).1.support : Set X) = closure {C.point} := by
    simp [toW]
  have h3 : closure {(toW sX C).genericPt} = closure {C.point} := by
    rw [← h2]; exact h1.symm
  exact ((inseparable_iff_closure_eq).mpr h3).eq

private theorem toW_injective : Function.Injective (toW sX) := by
  intro C C' h
  have h1 : (toW sX C).genericPt = (toW sX C').genericPt := by rw [h]
  rw [genericPt_toW, genericPt_toW] at h1
  exact Mori.ProperCurve.ext h1

private theorem exists_properCurve (hX : topologicalKrullDim X ≤ 1) [IsProper sX]
    (W : DimIntegralSubscheme (unitPushforward X) 1) :
    ∃ C : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X},
      toW sX C.1 = W := by
  have hint := W.2.1
  have hW : W.1 = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({W.genericPt} : Set X)) := eq_vanishingIdeal_closure_genericPt W.1
  have hdim : topologicalKrullDim W.1.subscheme = 1 := by simpa using W.2.2.2
  have hpc : Mori.IsProperCurve sX W.genericPt := by
    refine ⟨?_, ?_⟩
    · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({W.genericPt} : Set X))).subscheme = 1
      rw [← hW]; exact hdim
    · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({W.genericPt} : Set X))).subschemeι ≫ sX)
      rw [← hW]; infer_instance
  exact ⟨⟨⟨W.genericPt, hpc⟩, closure_genericPt_mem_irreducibleComponents hX W.1 hdim⟩,
    Subtype.ext hW.symm⟩

end toW

private theorem finsum_dimIntegral_eq {K : Type u} [Field K]
    (sX : X ⟶ Spec (.of K)) [IsProper sX] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    invertibleCurveDegree K sX hX M =
      ∑ᶠ W : DimIntegralSubscheme (unitPushforward X) 1,
        Stacks.Chow.sheafMultiplicity (unitPushforward X) W.genericPt *
        invertibleCurveDegree K (W.1.subschemeι ≫ sX) W.topologicalKrullDim_le
          ((Scheme.Modules.pullback W.1.subschemeι).obj M) := by
  have h := intersectionNumber_eq_sum_dimComponents K sX (𝟙 X) 1 hX (fun _ => M)
  rw [intersectionNumber_one_eq_invertibleCurveDegree] at h
  have e := invertibleCurveDegree_congr_structure (Category.id_comp sX) hX
    (L := (Scheme.Modules.pullback (𝟙 X)).obj M)
  rw [e] at h
  have e2 : (Scheme.Modules.pullback (𝟙 X)).obj M ≅ M := (Scheme.Modules.pullbackId X).app M
  rw [← invertibleCurveDegree_eq_of_iso K sX hX e2]
  rw [h]
  refine finsum_congr fun W => ?_
  exact congrArg _ (intersectionNumber_one_eq_invertibleCurveDegree K sX _ _ M)

end dimComponents

/-- **Degree dictionary on a proper curve.** Let `X` be proper over a field `K`, of dimension at
most one, and `M` invertible on `X`. For every choice of normalizations `ν_C : C̃ ⟶ C` of the
one-dimensional irreducible components `C` of `X`,
`∑_C m_C deg(ν_C^* M) = χ(X, M) - χ(X, 𝒪_X)`, where `m_C` is the length of `𝒪_{X,η_C}`. -/
private theorem finsum_length_mul_degreeOn_eq_invertibleCurveDegree {K : Type*} [Field K]
    {X : Scheme} (sX : X ⟶ Spec (.of K)) [IsProper sX] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (N : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} → Scheme)
    (ν : ∀ C, N C ⟶ C.1.scheme) (hν : ∀ C, IsCurveNormalization (ν C))
    (hNdim : ∀ C, topologicalKrullDim (N C) ≤ 1) :
    ∑ᶠ C, ((Module.length (X.presheaf.stalk C.1.point)
        (X.presheaf.stalk C.1.point)).toNat : ℤ) *
      (haveI := (hν C).isFinite
       haveI : IsProper ((ν C ≫ C.1.ι) ≫ sX) := by
         rw [Category.assoc]; infer_instance
       Mori.degreeOn K sX (ν C ≫ C.1.ι) (hNdim C) M) =
      invertibleCurveDegree K sX hX M := by
  classical
  rw [finsum_dimIntegral_eq sX hX M]
  let e := Equiv.ofBijective
    (fun C : {C : Mori.ProperCurve sX // closure {C.point} ∈ irreducibleComponents X} =>
      toW sX C.1) ⟨fun C C' h => Subtype.ext (toW_injective sX h),
      fun W => exists_properCurve sX hX W⟩
  refine Eq.trans (finsum_congr fun C => ?_) (finsum_comp_equiv e)
  change _ = Stacks.Chow.sheafMultiplicity (unitPushforward X) (toW sX C.1).genericPt * _
  rw [sheafMultiplicity_unitPushforward, genericPt_toW]
  congr 1
  have := (hν C).isFinite
  have : IsProper ((ν C ≫ C.1.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  exact degreeOn_normalization C.1 (hν C) (hNdim C) M

section flatClosure

private theorem flat_of_stalk_torsionFree {Y Z : Scheme.{u}} (q : Y ⟶ Z)
    (hdom : ∀ z : Z, IsDomain (Z.presheaf.stalk z)) (hB : ∀ z : Z, IsBezout (Z.presheaf.stalk z))
    (h : ∀ x : Y, ∀ a : Z.presheaf.stalk (q x), a ≠ 0 → ∀ s : Y.presheaf.stalk x,
      (q.stalkMap x).hom a * s = 0 → s = 0) : Flat q := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  have := hdom (q x)
  have := hB (q x)
  let : Algebra (Z.presheaf.stalk (q x)) (Y.presheaf.stalk x) := (q.stalkMap x).hom.toAlgebra
  change (algebraMap (Z.presheaf.stalk (q x)) (Y.presheaf.stalk x)).Flat
  rw [RingHom.flat_algebraMap_iff, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  refine ⟨fun a ha s t hst => ?_⟩
  have hne : a ≠ 0 := ha.ne_zero
  have h1 : a • s = a • t := hst
  refine sub_eq_zero.mp (h x a hne (s - t) ?_)
  rw [mul_sub]
  exact sub_eq_zero.mpr h1

/-- A regular local ring of dimension at most one is a Bézout domain: it is a field or a discrete
valuation ring. -/
private theorem isBezout_of_isRegularLocalRing (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsRegularLocalRing A] (hA : ringKrullDim A ≤ 1) : IsBezout A := by
  haveI := IsRegularLocalRing.isDomain A
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim A = n := by
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := A))
    have hmt : m ≠ ⊤ := by
      rintro rfl
      rw [← hm] at hA
      exact absurd hA (by decide)
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hmt
    exact ⟨n, hm.symm⟩
  rw [hn] at hA
  have hn1 : n ≤ 1 := by exact_mod_cast hA
  interval_cases n
  · have : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by rw [hn])
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := A)).toField
    infer_instance
  · haveI : IsDiscreteValuationRing A :=
      ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one A (by exact_mod_cast hn)).out 1 3).mp
        ‹IsRegularLocalRing A›
    infer_instance

private theorem stalk_domain_bezout {k : Type u} [Field k] {Δ : Scheme.{u}}
    (sΔ : Δ ⟶ Spec (.of k)) [ConnectedSpace Δ] (hsm : SmoothOfRelativeDimension 1 sΔ) (z : Δ) :
    IsDomain (Δ.presheaf.stalk z) ∧ IsBezout (Δ.presheaf.stalk z) := by
  have : Smooth sΔ := hsm.smooth
  have : IsLocallyNoetherian Δ := LocallyOfFiniteType.isLocallyNoetherian sΔ
  have := isRegularLocalRing_stalk_of_smooth_over_field sΔ z
  have : Nonempty Δ := ⟨z⟩
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 sΔ
  have h1 : ringKrullDim (Δ.presheaf.stalk z) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have := coheight_le_topologicalKrullDim z
    rw [hdim] at this
    simpa using this
  exact ⟨IsRegularLocalRing.isDomain _,
    isBezout_of_isRegularLocalRing _ h1⟩

private theorem stalk_torsionFree_of_injective_app {Gb U Δ : Scheme.{u}} [IsIntegral Δ]
    (t : U ⟶ Gb) (q : Gb ⟶ Δ)
    (hinj : ∀ W : Gb.Opens, Function.Injective (t.app W))
    (hreg : ∀ u : U, ∀ b : Δ.presheaf.stalk ((t ≫ q) u), b ≠ 0 →
      ∀ c : U.presheaf.stalk u, ((t ≫ q).stalkMap u).hom b * c = 0 → c = 0)
    (x : Gb) (a : Δ.presheaf.stalk (q x)) (ha : a ≠ 0) (s : Gb.presheaf.stalk x)
    (h : (q.stalkMap x).hom a * s = 0) : s = 0 := by
  obtain ⟨M, hxM, α, rfl⟩ := Δ.presheaf.exists_germ_eq a
  have hx0 : x ∈ q ⁻¹ᵁ M := hxM
  obtain ⟨N, hNle, hxN, σ, rfl⟩ := Gb.presheaf.exists_le_germ_eq s hx0
  rw [Scheme.Hom.germ_stalkMap_apply, ← Gb.presheaf.germ_res_apply (homOfLE hNle) x hxN,
    ← map_mul] at h
  have h0 : Gb.presheaf.germ N x hxN
      (Gb.presheaf.map (homOfLE hNle).op (q.app M α) * σ) =
      Gb.presheaf.germ N x hxN 0 := by rw [h, map_zero]
  obtain ⟨W, hxW, iW, iW', hW⟩ := Gb.presheaf.germ_eq x hxN hxN _ _ h0
  obtain rfl : iW = iW' := Subsingleton.elim _ _
  have hWle : W ≤ q ⁻¹ᵁ M := iW.le.trans hNle
  set A := Gb.presheaf.map (homOfLE hWle).op (q.app M α) with hA
  set τ := Gb.presheaf.map iW.op σ with hτ
  have hAτ : A * τ = 0 := by
    have : Gb.presheaf.map iW.op (Gb.presheaf.map (homOfLE hNle).op (q.app M α) * σ) = 0 := by
      rw [hW, map_zero]
    rw [map_mul] at this
    have hA' : Gb.presheaf.map iW.op (Gb.presheaf.map (homOfLE hNle).op (q.app M α)) = A := by
      rw [hA, ← ConcreteCategory.comp_apply, ← Gb.presheaf.map_comp]
      rfl
    rwa [hA'] at this
  have hs : Gb.presheaf.germ N x hxN σ = Gb.presheaf.germ W x hxW τ := by
    rw [hτ, Gb.presheaf.germ_res_apply]
  rw [hs]
  have hτ0 : τ = 0 := by
    apply hinj W
    rw [map_zero]
    refine TopCat.Presheaf.section_ext U.sheaf (t ⁻¹ᵁ W) _ 0 fun u hu => ?_
    change U.presheaf.germ (t ⁻¹ᵁ W) u hu ((t.app W) τ) = U.presheaf.germ (t ⁻¹ᵁ W) u hu 0
    have htu : t u ∈ W := hu
    have hqM : q (t u) ∈ M := hWle htu
    have hα : α ≠ 0 := by
      rintro rfl
      exact ha (map_zero _)
    have hb : Δ.presheaf.germ M ((t ≫ q) u) hqM α ≠ 0 := fun hb0 =>
      hα (germ_injective_of_isIntegral Δ _ hqM (hb0.trans (map_zero _).symm))
    refine Eq.trans (hreg u _ hb _ ?_) (map_zero (U.presheaf.germ (t ⁻¹ᵁ W) u hu).hom).symm
    have e2 : ((t ≫ q).stalkMap u).hom (Δ.presheaf.germ M ((t ≫ q) u) hqM α) =
        U.presheaf.germ (t ⁻¹ᵁ W) u hu (t.app W A) := by
      rw [Scheme.Hom.stalkMap_comp]
      change (t.stalkMap u).hom ((q.stalkMap (t u)).hom (Δ.presheaf.germ M (q (t u)) hqM α)) = _
      rw [Scheme.Hom.germ_stalkMap_apply q M (t u) hqM,
        Scheme.Hom.germ_stalkMap_apply t (q ⁻¹ᵁ M) u hqM, hA]
      have nat : t.app W (Gb.presheaf.map (homOfLE hWle).op (q.app M α)) =
          U.presheaf.map ((Opens.map t.base).map (homOfLE hWle)).op
            (t.app (q ⁻¹ᵁ M) (q.app M α)) :=
        (ConcreteCategory.congr_hom (Scheme.Hom.naturality t (homOfLE hWle).op) (q.app M α))
      rw [nat, TopCat.Presheaf.germ_res_apply]
    rw [e2, ← map_mul, ← map_mul, hAτ, map_zero, map_zero]
  rw [hτ0, map_zero]

/-- A nonzero element of a domain stalk of the target of a flat morphism is a nonzerodivisor on
the stalks of the source. -/
private theorem stalkMap_mul_eq_zero_of_flat {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Flat f] (y : Y)
    [IsDomain (Z.presheaf.stalk (f y))] (b : Z.presheaf.stalk (f y)) (hb : b ≠ 0)
    (c : Y.presheaf.stalk y) (hc : (f.stalkMap y).hom b * c = 0) : c = 0 := by
  let : Algebra (Z.presheaf.stalk (f y)) (Y.presheaf.stalk y) := (f.stalkMap y).hom.toAlgebra
  have : Module.Flat (Z.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    RingHom.flat_algebraMap_iff.mp ((Flat.iff_flat_stalkMap f).mp ‹_› y)
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb) ?_
  change b • c = b • 0
  rwa [smul_zero, Algebra.smul_def]

end flatClosure

/-- **Hartshorne III.9.7.** Over a connected smooth curve `Δ`, the scheme-theoretic closure of
an open `U ⊆ G₁` of a proper `Δ`-scheme which lies over an open `V ⊆ Δ` and is flat over it
is flat over `Δ`. -/
private theorem flat_imageι_comp_of_flat_resLE {k : Type*} [Field k] {Δ : Scheme}
    (sΔ : Δ ⟶ Spec (.of k)) [ConnectedSpace Δ] (hsm : SmoothOfRelativeDimension 1 sΔ)
    (V : Δ.Opens) {G₁ : Scheme} (p : G₁ ⟶ Δ) [IsProper p]
    (U : G₁.Opens) (hUV : U ≤ p ⁻¹ᵁ V) (hflat : Flat (p.resLE V U hUV)) :
    Flat (U.ι.imageι ≫ p) := by
  have : Smooth sΔ := hsm.smooth
  have : IsIntegral Δ := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth sΔ
  have : IsLocallyNoetherian G₁ := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sΔ)
  refine flat_of_stalk_torsionFree _ (fun z => (stalk_domain_bezout sΔ hsm z).1)
    (fun z => (stalk_domain_bezout sΔ hsm z).2) ?_
  intro x a ha s hs
  refine stalk_torsionFree_of_injective_app U.ι.toImage (U.ι.imageι ≫ p) ?_ ?_ x a ha s hs
  · intro W
    exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat)
      (F := U.ι.image.sheaf) U.ι.toImage.c W
      (fun y _ => Scheme.Hom.stalkFunctor_toImage_injective U.ι y)
  · have : Flat (U.ι.toImage ≫ U.ι.imageι ≫ p) := by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← Scheme.Hom.resLE_comp_ι p hUV]
      infer_instance
    intro u b hb c hc
    have := (stalk_domain_bezout sΔ hsm ((U.ι.toImage ≫ U.ι.imageι ≫ p) u)).1
    exact stalkMap_mul_eq_zero_of_flat _ u b hb c hc

/-- **Degrees on the fibres of a proper flat family of curves.** (cf. Hartshorne III.9.7.) Let
`π : G ⟶ Δ` be proper and flat, with `Δ` a connected smooth curve over `k` or `Spec k`, `G` of
finite type over `k`, and all fibres of dimension at most one; let `L` be invertible on `G`.

1. For every closed point `t ∈ Δ` and every choice of normalizations `νᵢ : C̃ᵢ ⟶ Cᵢ` of the
   one-dimensional irreducible components `Cᵢ` of `G_t`,
   `∑ᵢ mᵢ deg(νᵢ^* L) = χ(G_t, L|_{G_t}) - χ(G_t, 𝒪_{G_t})`, where `mᵢ` is the length of the
   local ring of `G_t` at the generic point of `Cᵢ`.
2. `χ(G_t, L|_{G_t}) - χ(G_t, 𝒪_{G_t})` is the same for all closed points `t`.
3. If `Δ` is a smooth curve, `Δ° ⊆ Δ` is dense open, `p : G₁ ⟶ Δ` is proper and `G° ⊆ G₁` is an
   open subscheme over `Δ°` which is flat over `Δ°`, then the scheme-theoretic closure of `G°` in
   `G₁` is proper and flat over `Δ`. -/
@[mmp "lem_mmp_foundation_fa2_proper_flat_curve_degree"]
public theorem fibre_degree_eq_and_isProper_flat_closure {k : Type*} [Field k]
    {G Δ : Scheme} (sΔ : Δ ⟶ Spec (.of k)) (π : G ⟶ Δ) [IsProper π] [Flat π]
    [LocallyOfFiniteType (π ≫ sΔ)] [QuasiCompact (π ≫ sΔ)] [ConnectedSpace Δ]
    (hΔ : SmoothOfRelativeDimension 1 sΔ ∨ IsIso sΔ)
    (hdim : ∀ t : Δ, topologicalKrullDim (π.fiber t) ≤ 1)
    (L : G.Modules) [SheafOfModules.IsInvertible G.presheaf G.ringCatSheaf.2 L] :
    haveI : ∀ t : Δ, IsProper (π.fiberToSpecResidueField t) := fun t =>
      IsProper.isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback π (Δ.fromSpecResidueField t)) ‹_›
    (∀ t : Δ, IsClosed ({t} : Set Δ) →
      ∀ (N : {C : Mori.ProperCurve (π.fiberToSpecResidueField t) //
              closure {C.point} ∈ irreducibleComponents (π.fiber t)} → Scheme)
        (ν : ∀ C, N C ⟶ C.1.scheme) (hν : ∀ C, IsCurveNormalization (ν C))
        (hNdim : ∀ C, topologicalKrullDim (N C) ≤ 1),
        ∑ᶠ C, ((Module.length ((π.fiber t).presheaf.stalk C.1.point)
            ((π.fiber t).presheaf.stalk C.1.point)).toNat : ℤ) *
          (haveI := (hν C).isFinite
           haveI : IsProper ((ν C ≫ C.1.ι) ≫ π.fiberToSpecResidueField t) := by
             rw [Category.assoc]; infer_instance
           Mori.degreeOn (Δ.residueField t) (π.fiberToSpecResidueField t) (ν C ≫ C.1.ι)
             (hNdim C) ((Scheme.Modules.pullback (π.fiberι t)).obj L)) =
        invertibleCurveDegree (Δ.residueField t) (π.fiberToSpecResidueField t) (hdim t)
          ((Scheme.Modules.pullback (π.fiberι t)).obj L)) ∧
    (∀ t t' : Δ, IsClosed ({t} : Set Δ) → IsClosed ({t'} : Set Δ) →
      invertibleCurveDegree (Δ.residueField t) (π.fiberToSpecResidueField t) (hdim t)
          ((Scheme.Modules.pullback (π.fiberι t)).obj L) =
        invertibleCurveDegree (Δ.residueField t') (π.fiberToSpecResidueField t') (hdim t')
          ((Scheme.Modules.pullback (π.fiberι t')).obj L)) ∧
    (SmoothOfRelativeDimension 1 sΔ →
      ∀ (V : Δ.Opens), Dense (V : Set Δ) →
      ∀ (G₁ : Scheme) (p : G₁ ⟶ Δ) [IsProper p] (U : G₁.Opens) (hUV : U ≤ p ⁻¹ᵁ V),
        Flat (p.resLE V U hUV) →
        IsProper (U.ι.imageι ≫ p) ∧ Flat (U.ι.imageι ≫ p)) := by
  have : LocallyOfFiniteType sΔ := by
    rcases hΔ with h | h
    · have : Smooth sΔ := h.smooth
      infer_instance
    · infer_instance
  have : IsLocallyNoetherian Δ := LocallyOfFiniteType.isLocallyNoetherian sΔ
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π sΔ
  refine ⟨fun t _ N ν hν hNdim => ?_, fun t t' _ _ => ?_, ?_⟩
  · exact @finsum_length_mul_degreeOn_eq_invertibleCurveDegree _ _ _
      (π.fiberToSpecResidueField t)
      (IsProper.isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback π (Δ.fromSpecResidueField t)) ‹_›) (hdim t) _ _ N ν hν hNdim
  · exact (MMP.fibreEulerCharacteristic_tensorPowModule_eq π L).2 hdim t t'
  · intro hsm V _ G₁ p _ U hUV hflat
    exact ⟨inferInstance, flat_imageι_comp_of_flat_resLE sΔ hsm V p U hUV hflat⟩

end MMP.Flips
