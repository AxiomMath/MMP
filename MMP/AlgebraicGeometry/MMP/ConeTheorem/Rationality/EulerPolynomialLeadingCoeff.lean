module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.Surface.RegularSurfaceBlowup
public import MMP.AlgebraicGeometry.Intersection.GenericallyFinitePullback
public import MMP.AlgebraicGeometry.Positivity.BigCartierCriteria
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation

/-!
# The Euler characteristic function of a rationality datum is a nonzero polynomial

Let `(X, Δ, a, H)` be a rationality datum of dimension `n`, `g : Y ⟶ X` a log resolution of
`(X, Δ)` with `Y` projective, and `A` a `ℚ`-divisor on `Y`. The Euler characteristic function
`P(x, y) = χ(Y, 𝒪_Y(x g^*H + y g^*(a(K_X + Δ)) + ⌈A⌉))` is the restriction to `ℤ²` of a nonzero
polynomial with rational coefficients, and its coefficient of `xⁿ` is `(Hⁿ) / n!`, where the
self-intersection number `(Hⁿ)` is positive.

Write `H' = g^*H` and `B' = g^*(a(K_X + Δ))`. The function `P(x, y) = χ(Y, 𝒪_Y(x H' + y B' +
⌈A⌉))` is a polynomial of degree at most `n` whose degree-`n` part is `((x H' + y B')ⁿ) / n!`;
its coefficient of `xⁿ` is `(H'ⁿ) / n!`. Since `g` is
birational, `(H'ⁿ) = (Hⁿ)` by the projection formula, and `H'` is nef (its degree on a curve `C`
is `0` or `[k(C) : k(g(C))] (H · g(C))`) and big (pulling back sections embeds
`H⁰(X, 𝒪_X(mH))` into `H⁰(Y, 𝒪_Y(mH'))`) on the projective variety `Y`, so `(H'ⁿ) > 0`.

## Main results

* `MMP.Mori.IsRationalityDatum.coeff_eulerPolynomial_of_isLogResolution`: the statement above.

## Implementation notes

As in `MMP.Mori.IsStripAdaptedResolution`, the pull-backs `g^*H` and `g^*(a(K_X + Δ))` are
divisors `H'` and `B'` on `Y` satisfying `MMP.Mori.Divisor.IsPullback`, and the integral divisor
`a(K_X + Δ)` is `⌊a(K_X + Δ)⌋`. The polynomial is an `MvPolynomial (Fin 2) ℚ`, the variable `0`
being `x` (the coefficient of `g^*H`) and the variable `1` being `y`; since a polynomial
vanishing on `ℤ²` is zero, it is determined by its values, and the coefficient is computed for
every polynomial interpolating `P`. The dimension `n` enters the intersection number through
`topologicalKrullDim X = n`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4, Step 5
-/

open CategoryTheory AlgebraicGeometry MMP.Mori Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori.RationalityEulerPolynomialProof

/-- The coefficient of `xⁿ` in a polynomial in `x, y` is the value at `(1, 0)` of its
homogeneous component of degree `n`. -/
private theorem coeff_single_zero_eq_eval_homogeneousComponent (P : MvPolynomial (Fin 2) ℚ)
    (n : ℕ) :
    P.coeff (Finsupp.single 0 n) =
      MvPolynomial.eval (fun i => ((![1, 0] : Fin 2 → ℤ) i : ℚ))
        (MvPolynomial.homogeneousComponent n P) := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, map_sum,
    Finset.sum_eq_single (Finsupp.single 0 n)]
  · simp [MvPolynomial.eval_monomial, Finsupp.prod_single_index]
  · intro d hd hne
    obtain ⟨-, hdeg⟩ := Finset.mem_filter.mp hd
    have h1 : d 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Finsupp.single_eq_same]
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, h1] at hdeg
        simpa using hdeg
      · simp [h1]
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [zero_pow h1]
  · intro h
    rw [Finset.mem_filter, not_and_or] at h
    rcases h with h | h
    · rw [MvPolynomial.mem_support_iff, not_not] at h
      simp [h]
    · exact absurd (by simp [Finsupp.degree_single]) h

/-- Equal families of invertible sheaves have equal intersection numbers. -/
private theorem intersectionNumber_congr_family (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ d) {L M : Fin d → X.Modules}
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (h : L = M) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  subst h
  rfl

/-- The intersection number depends on the family of invertible sheaves only through the
isomorphism classes of its members. -/
private theorem intersectionNumber_eq_of_iso (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ d) (L M : Fin d → X.Modules)
    [hL : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [hM : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (e : ∀ q, L q ≅ M q) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  classical
  let N : ℕ → Fin d → X.Modules := fun t q => if (q : ℕ) < t then M q else L q
  have hN : ∀ t q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N t q) := by
    intro t q
    dsimp only [N]
    split
    · exact hM q
    · exact hL q
  have key : ∀ t, intersectionNumber k f i d hd L = intersectionNumber k f i d hd (N t) := by
    intro t
    induction t with
    | zero =>
      exact intersectionNumber_congr_family k f i d hd (funext fun q => (if_neg (by omega)).symm)
    | succ t ih =>
      rw [ih]
      by_cases ht : t < d
      · refine intersectionNumber_eq_of_iso_at k f i d hd (N t) (N (t + 1)) ⟨t, ht⟩
          (fun q hq => ?_) ?_
        · have : (q : ℕ) ≠ t := fun h => hq (Fin.ext h)
          dsimp only [N]
          by_cases h : (q : ℕ) < t
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]
        · exact eqToIso (if_neg (lt_irrefl t)) ≪≫ e ⟨t, ht⟩ ≪≫
            eqToIso (if_pos (Nat.lt_succ_self t)).symm
      · exact intersectionNumber_congr_family k f i d hd (funext fun q => by
          dsimp only [N]
          rw [if_pos (by omega : (q : ℕ) < t), if_pos (by omega : (q : ℕ) < t + 1)])
  rw [key d]
  exact intersectionNumber_congr_family k f i d hd (funext fun q => if_pos q.2)

section Sections

variable {k : Type u} [Field k]

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{u}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{u}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{u}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (W : X.Opens) (hW : W ≤ b ⁻¹ᵁ K) :
    Function.Bijective (fun c : Γ(X, W) =>
      c • ((Scheme.Modules.pullback b).obj A).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a)) := by
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) _ (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (op K) a)
    _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : Γ(L, ⊤)) (hs : L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0) : s = 0 := by
  have hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  have key : ∀ x : X, ∃ (K : X.Opens) (_ : x ∈ K),
      L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s = 0 := by
    intro x
    obtain ⟨K, hx, a, ha⟩ : ∃ (K : X.Opens) (_ : x ∈ K) (a : Γ(L, K)), ∀ (W : X.Opens)
        (hW : W ≤ K), Function.Bijective
          (fun c : Γ(X, W) => c • L.presheaf.map (homOfLE hW).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible X.toRingedSpace _ L hL x
    refine ⟨K, hx, ?_⟩
    obtain ⟨g, hg⟩ := (ha K le_rfl).2 (L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s)
    simp only [map_homOfLE_refl] at hg
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter K.2 V.2 ⟨x, hx⟩ hV
    have : Nonempty (K ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
    have hg0 : g = 0 := by
      refine map_injective_of_isIntegral X (homOfLE inf_le_left : K ⊓ V ⟶ K) ?_
      rw [map_zero]
      refine (ha (K ⊓ V) inf_le_left).1 ?_
      dsimp only
      rw [zero_smul, ← Scheme.Modules.map_smul, hg, map_map_homOfLE,
        ← map_map_homOfLE L (inf_le_right : K ⊓ V ≤ V) (le_top : V ≤ ⊤), hs, map_zero]
    rw [← hg, hg0, zero_smul]
  choose K hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K ⊤
    (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxK x⟩) s 0
    fun x => ?_
  change L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op s =
    L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op 0
  rw [hK x, map_zero]

/-- Pull-back of sections of an invertible sheaf along a dominant quasi-compact morphism of
integral schemes is injective on global sections. -/
private theorem unit_app_top_injective {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
    (g : Y ⟶ T) [IsDominant g] [QuasiCompact g] (M : T.Modules)
    [Stacks.Ample.IsInvertibleModule T M] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤) := by
  have hMinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (structureSheafRing T.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  set L := (Scheme.Modules.pullback g).obj M
  set η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨y0⟩ : Nonempty Y := inferInstance
  obtain ⟨K, hyK, a, ha⟩ : ∃ (K : T.Opens) (_ : g y0 ∈ K) (a : Γ(M, K)), ∀ (W : T.Opens)
      (hW : W ≤ K), Function.Bijective
        (fun c : Γ(T, W) => c • M.presheaf.map (homOfLE hW).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible T.toRingedSpace _ M hMinv (g y0)
  obtain ⟨U, hUaff, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyK
  set e : Γ(L, g ⁻¹ᵁ U) := η.app U (M.presheaf.map (homOfLE hUK).op a)
  have hgen := bijective_smul_unit_app g M (M.presheaf.map (homOfLE hUK).op a)
    (fun W hW => by simpa only [map_map_homOfLE] using ha W (hW.trans hUK)) (g ⁻¹ᵁ U) le_rfl
  set t := M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (ha U hUK).2 t
  have hηt : η.app U t = 0 := by
    refine (PresheafOfModules.naturality_apply η.val (homOfLE le_top : U ⟶ ⊤).op s).trans ?_
    change _ = (0 : _)
    erw [hs, map_zero]
    rfl
  have hgf : g.app U f = 0 := by
    refine hgen.1 ?_
    change g.app U f • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e =
      (0 : Γ(Y, g ⁻¹ᵁ U)) • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e
    rw [map_homOfLE_refl, zero_smul]
    refine Eq.trans ?_ hηt
    rw [← hf, Scheme.Modules.Hom.app_smul]
    rfl
  have : IsSchemeTheoreticallyDominant g := .of_isDominant _
  have hf0 : f = 0 := g.app_injective U (by rw [hgf, map_zero])
  have ht0 : t = 0 := by
    rw [← hf, hf0]
    exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- An `R`-linear equivalence between `R`-modules that are `k`-vector spaces through a ring map
`φ : k →+* R` preserves the `k`-dimension. -/
private theorem finrank_compHom_eq {R : Type u} [CommRing R] (φ : k →+* R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) :
    (letI := Module.compHom M φ; Module.finrank k M) =
      (letI := Module.compHom N φ; Module.finrank k N) := by
  letI := Module.compHom M φ
  letI := Module.compHom N φ
  let g' : M ≃ₗ[k] N :=
    { g.toEquiv with map_add' := g.map_add, map_smul' := fun c x => g.map_smul (φ c) x }
  exact g'.finrank_eq

/-- The `Γ(X, 𝒪_X)`-linear isomorphism `Γ(X, L) ≃ Γ(X, L')` induced by an isomorphism `L ≅ L'`. -/
private noncomputable def sectionsLinearEquiv {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(L', ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  map_add' := map_add _
  map_smul' _ s := Scheme.Modules.Hom.app_smul e.hom _ s
  left_inv s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  right_inv s := by
    change ((e.inv ≫ e.hom).app ⊤) s = s
    rw [Iso.inv_hom_id]
    rfl

/-- The `k`-structure on global sections, written through `Scheme.Hom.appLE`. -/
private theorem scalarsToGlobalSections_eq' {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

/-- The global sections of `𝒪_X(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsProper sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {D : Divisor X} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sX
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sX D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sX D.divisorialSheaf).toLinearEquiv
  have key : ∀ ψ : k →+* Γ(X, ⊤),
      ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom (D.divisorialSubmodule ⊤) ψ;
          Module.Finite k (D.divisorialSubmodule ⊤)) := by
    rintro ψ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq' sX)

/-- `h⁰` of a Cartier divisor `A` equals `h⁰` of a divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`. -/
private theorem cartierH0_eq_h0 {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    [IsNormal X] (A : X.CartierDivisor) (D : Divisor X)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    cartierH0 k sX A = D.h0 k sX :=
  finrank_compHom_eq (scalarsToGlobalSections k sX) (sectionsLinearEquiv e)

/-- For a Cartier divisor `A` and a Cartier divisor `D` with `𝒪_X(A) ≅ 𝒪_X(D)`, the
isomorphisms `𝒪_X((n + 1) A) ≅ 𝒪_X((n + 1) D)`. -/
private noncomputable def sheafSuccNsmulIso {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (A : X.CartierDivisor) (D : Divisor X) (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf A ≅ D.divisorialSheaf) :
    ∀ n : ℕ, MMP.CartierDivisor.sheaf ((n + 1) • A) ≅
      ((n + 1) • D).divisorialSheaf
  | 0 => eqToIso (by rw [zero_add, one_smul]) ≪≫ e ≪≫ eqToIso (by rw [zero_add, one_smul])
  | n + 1 => eqToIso (by rw [succ_nsmul]) ≪≫
      (MMP.CartierDivisorSheaf.sheafMulIso ((n + 1) • A) A).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X (sheafSuccNsmulIso A D hD e n) e ≪≫
      (hD.nsmul (n + 1)).divisorialSheafTensorIso hD ≪≫ eqToIso (by rw [← succ_nsmul])

/-- **Pulling back sections.** For a dominant morphism `g : Y ⟶ X` of integral normal schemes,
`Y` proper over `k`, and Cartier divisors `D` on `X` and `D'` on `Y` with
`𝒪_Y(D') ≅ g^*𝒪_X(D)`, `h⁰(X, 𝒪_X(D)) ≤ h⁰(Y, 𝒪_Y(D'))`. -/
private theorem h0_le_h0_of_iso_pullback {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) [IsDominant g] [QuasiCompact g]
    [IsProper (g ≫ sX)] {D : Divisor X} (hD : D.IsCartier) {D' : Divisor Y} (hD' : D'.IsCartier)
    (e : D'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj D.divisorialSheaf) :
    D.h0 k sX ≤ D'.h0 k (g ≫ sX) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have hsc : ∀ c, g.appTop (scalarsToGlobalSections k sX c) =
      scalarsToGlobalSections k (g ≫ sX) c := by
    intro c
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  set M := D.divisorialSheaf
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  letI := Module.compHom Γ(M, ⊤) (scalarsToGlobalSections k sX)
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k (g ≫ sX))
  have : Module.Finite k (D'.divisorialSubmodule ⊤) := finite_divisorialSubmodule_top (g ≫ sX) hD'
  let φ : Γ(M, ⊤) →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun s := e.inv.app ⊤ (η.app ⊤ s)
      map_add' s t := by
        rw [map_add]
        exact map_add _ _ _
      map_smul' c s := by
        change e.inv.app ⊤ (η.app ⊤ (scalarsToGlobalSections k sX c • s)) =
          (scalarsToGlobalSections k (g ≫ sX) c •
            (e.inv.app ⊤ (η.app ⊤ s) : D'.divisorialSubmodule ⊤))
        rw [Scheme.Modules.Hom.app_smul, ← hsc c]
        exact Scheme.Modules.Hom.app_smul e.inv _ _ }
  have h2 : ∀ x, e.hom.app ⊤ (e.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  have hφ : Function.Injective φ := fun s t hst => by
    refine unit_app_top_injective g M ?_
    have := congrArg (e.hom.app ⊤) hst
    change e.hom.app ⊤ (e.inv.app ⊤ (η.app ⊤ s)) = e.hom.app ⊤ (e.inv.app ⊤ (η.app ⊤ t)) at this
    exact (h2 _).symm.trans (this.trans (h2 _))
  unfold Divisor.h0
  letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sX)
  exact LinearMap.finrank_le_finrank_of_injective (f := (φ : D.divisorialSubmodule ⊤ →ₗ[k] _)) hφ

end Sections

section Pullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace Y] {sX : X ⟶ Spec (.of k)} [IsProper sX] {g : Y ⟶ X} [IsProper g] [IsDominant g]
  {H : Divisor X} {H' : Divisor Y}

/-- **Birational invariance of the top self-intersection.** If `g : Y ⟶ X` is a proper
birational morphism of `n`-dimensional varieties and `𝒪_Y(H') ≅ g^*𝒪_X(H)`, then
`(H'ⁿ) = (Hⁿ)`: the projection formula has the factor `[k(Y) : k(X)] = 1`. -/
private theorem intersectionNumberOn_eq_of_iso_pullback (hbir : IsBirationalMorphism g) {n : ℕ}
    (hn : topologicalKrullDim X = n) (hnY : topologicalKrullDim Y = n) (hH : H.IsCartier)
    (hH'c : H'.IsCartier)
    (e : H'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj H.divisorialSheaf) :
    Divisor.intersectionNumberOn k (g ≫ sX) (𝟙 Y) n hnY.le (fun _ => H') (fun _ => hH'c) =
      Divisor.intersectionNumberOn k sX (𝟙 X) n hn.le (fun _ => H) (fun _ => hH) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hH'c.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj H.divisorialSheaf) :=
    MMP.Mori.isInvertible_pullback_obj g _
  have h1 := sheafIntersectionNumber_pullback_eq_finrank_mul k sX g n hn hnY
    (fun _ => H.divisorialSheaf)
  letI := functionFieldMapAlgebra g
  rw [← (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField)
    hbir.functionFieldMap_bijective).toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one,
    one_mul] at h1
  unfold Divisor.intersectionNumberOn
  rw [← h1, Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_eq_of_iso k _ _ n _ _ _ fun _ => e

/-- **The pull-back of a nef divisor is nef.** The degree of `g^*𝒪_X(H)` on a curve `C ⊆ Y` is
`0` when `g` contracts `C` and `[k(C) : k(g(C))] (H · g(C)) ≥ 0` otherwise. -/
private theorem isNef_of_iso_pullback [AlgebraicGeometry.IsProperVariety k sX]
    [AlgebraicGeometry.IsProperVariety k (g ≫ sX)] (hH : H.IsNef k sX) (hH'c : H'.IsCartier)
    (e : H'.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj H.divisorialSheaf) :
    H'.IsNef k (g ≫ sX) := by
  have hHc : H.IsCartier := hH.1
  haveI := hHc.isInvertibleModule_divisorialSheaf
  haveI := hH'c.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj H.divisorialSheaf) :=
    MMP.Mori.isInvertible_pullback_obj g _
  rw [Divisor.isNef_iff k _ _ hH'c]
  intro Cv i _ _ _ hCv
  haveI : AlgebraicGeometry.IsCurve k (i ≫ g ≫ sX) :=
    (AlgebraicGeometry.isCurve_iff k _).mpr ⟨{}, hCv⟩
  rw [degreeOn_eq_of_iso k (g ≫ sX) i hCv.le e]
  by_cases hpt : ∃ x : X, Set.range (i ≫ g) = {x}
  · rw [degreeOn_pullback_divisorialSheaf_eq_zero (g ≫ sX) sX g i rfl H hHc hpt]
  have hc : (i ≫ g) ≫ sX = i ≫ g ≫ sX := Category.assoc _ _ _
  haveI : IsProper ((i ≫ g) ≫ sX) := by
    rw [hc]
    infer_instance
  haveI : AlgebraicGeometry.IsCurve k ((i ≫ g) ≫ sX) := by
    rw [hc]
    infer_instance
  haveI : IsProper (i ≫ g) := IsProper.of_comp (i ≫ g) sX
  haveI : IsProper ((i ≫ g).imageι ≫ sX) := isProper_imageι_comp (i ≫ g) sX
  have hcurve := isCurve_imageι_comp sX (i ≫ g) hpt
  haveI : IsIntegral (i ≫ g).image := hcurve.toIsIntegral
  have h := degreeOn_pullback_divisorialSheaf_eq_degreeOver_mul_intersectionNumber
    (g ≫ sX) sX g i rfl H hHc hcurve
  have hHC := ((QDivisor.isNef_toQDivisor_iff (k := k) (sX := sX) H hHc).mpr hH).2 _
    (i ≫ g).imageι hcurve.topologicalKrullDim_eq_one
  exact_mod_cast h ▸ mul_nonneg (by positivity) hHC

/-- **The pull-back of a big divisor is big.** Pulling back sections embeds `H⁰(X, 𝒪_X(mH))`
into `H⁰(Y, 𝒪_Y(mH'))` for `H'` the pull-back of `H` along `g`. -/
private theorem isBig_of_isPullback (hn : topologicalKrullDim X = topologicalKrullDim Y)
    (hH : H.IsCartier) (hH'c : H'.IsCartier)
    {hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp}
    (hH' : H.IsPullback g hHg H') (hbig : H.IsBig k sX) : H'.IsBig k (g ≫ sX) := by
  obtain ⟨d, hdX, c, hc, k₀, hk⟩ := hbig
  refine ⟨d, hn.symm.trans hdX, c, hc, k₀, fun m hm => (hk m hm).trans_le ?_⟩
  have hBm : ∀ Z, g (componentGenericPoint Y Z) ∉ (m • H).supp := fun Z hZ => hHg Z (by
    obtain ⟨E, hE, hx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    exact DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨E, fun h => hE (by rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]), hx⟩)
  exact_mod_cast h0_le_h0_of_iso_pullback sX g (hH.zsmul m) (hH'c.zsmul m)
    ((hH'.zsmul hH m hBm).divisorialSheafIso (hBc := hH.zsmul m))

end Pullback

/-- A Cartier divisor `C` with `𝒪_Y(C) ≅ 𝒪_Y(D)` for a big divisor `D` is big. -/
private theorem isBigCartier_of_iso {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ Spec (.of k))
    (C : Y.CartierDivisor) {D : Divisor Y} (hD : D.IsCartier)
    (e : MMP.CartierDivisor.sheaf C ≅ D.divisorialSheaf) (hbig : D.IsBig k f) :
    IsBigCartier k f C := by
  obtain ⟨d, hd, c, hc, k₀, hk⟩ := hbig
  refine ⟨d, hd, c, hc, max k₀ 1, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = ((j + 1 : ℕ) : ℤ) :=
    ⟨m.toNat - 1, by have := le_of_max_le_right hm; omega⟩
  have h := hk _ (le_of_max_le_left hm)
  rw [natCast_zsmul] at h ⊢
  rwa [cartierH0_eq_h0 f _ _ (sheafSuccNsmulIso C D hD e j)]

/-- **Nef and big divisors have positive top self-intersection.** On a projective variety `Y`
of dimension `n`, a nef and big Cartier divisor `D` satisfies `(Dⁿ) > 0`. -/
private theorem intersectionNumberOn_pos_of_isNef_of_isBig {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k f] {n : ℕ} (hn : topologicalKrullDim Y = n)
    {D : Divisor Y} (hD : D.IsCartier) (hnef : D.IsNef k f) (hbig : D.IsBig k f) :
    0 < Divisor.intersectionNumberOn k f (𝟙 Y) n hn.le (fun _ => D) (fun _ => hD) := by
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (f := f)
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  have hnefC : IsNef k f (MMP.CartierDivisor.sheaf C) := fun Cv i _ _ _ hCv =>
    degreeOn_eq_of_iso k f i hCv.le eC ▸ (D.isNef_iff k f hD).mp hnef Cv i hCv
  have hP := sheafSelfIntersectionNumber_pos_of_isNef_of_isBigCartier f hn C hnefC
    (isBigCartier_of_iso f C hD eC.symm hbig)
  unfold Divisor.intersectionNumberOn
  unfold sheafSelfIntersectionNumber at hP
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber] at hP ⊢
  rwa [intersectionNumber_eq_of_iso k _ _ n _ _ _ fun _ => eC]

end MMP.Mori.RationalityEulerPolynomialProof

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsProper sX]

open RationalityEulerPolynomialProof in
/-- **The Euler characteristic function of a rationality datum is a nonzero polynomial**
(Kollár–Mori 3.4, Step 5). Let `(X, Δ, a, H)` be a rationality datum of dimension `n`,
`g : Y ⟶ X` a log resolution of `(X, Δ)` with `Y` projective, `H'` and `B'` the pull-backs of
`H` and of `a(K_X + Δ)` to `Y`, and `A` a `ℚ`-divisor on `Y`. Then
`(x, y) ↦ χ(Y, 𝒪_Y(x H' + y B' + ⌈A⌉))` is the restriction to `ℤ²` of a nonzero polynomial
`P ∈ ℚ[x, y]`, the coefficient of `xⁿ` in any such `P` is `(Hⁿ) / n!`, and `(Hⁿ) > 0`. -/
@[mmp "lem_km3b_rationality_euler_polynomial_nonzero"]
public theorem IsRationalityDatum.coeff_eulerPolynomial_of_isLogResolution {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hd : IsRationalityDatum sX n K Δ a H) (hn : topologicalKrullDim X = n)
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {g : Y ⟶ X}
    (hg : IsLogResolution sX (QDivisor.toRDivisor Δ) g) (hY : IsProjectiveVariety k (g ≫ sX))
    {H' B' : Divisor Y}
    (hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp)
    (hH' : H.IsPullback g hHg H')
    (hBg : ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp)
    (hB' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback g hBg B')
    (A : QDivisor Y) :
    (∃ P : MvPolynomial (Fin 2) ℚ, P ≠ 0 ∧ ∀ u : Fin 2 → ℤ,
        MvPolynomial.eval (fun i => (u i : ℚ)) P =
          Divisor.eulerPolynomial k (g ≫ sX) ![H', B'] A u) ∧
      (∀ P : MvPolynomial (Fin 2) ℚ, (∀ u : Fin 2 → ℤ,
        MvPolynomial.eval (fun i => (u i : ℚ)) P =
          Divisor.eulerPolynomial k (g ≫ sX) ![H', B'] A u) →
        P.coeff (Finsupp.single 0 n) =
          (Divisor.intersectionNumberOn k sX (𝟙 X) n hn.le (fun _ => H)
            (fun _ => hd.isCartier_H) : ℚ) / n.factorial) ∧
      0 < Divisor.intersectionNumberOn k sX (𝟙 X) n hn.le (fun _ => H)
        (fun _ => hd.isCartier_H) := by
  have hsm : IsSmoothScheme (g ≫ sX) := hg.isSmoothScheme
  haveI : IsProper g := hg.isProper
  have hbir : IsBirationalMorphism g := hg.isBirationalMorphism
  haveI : IsDominant g := hbir.isDominant
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : AlgebraicGeometry.IsProperVariety k sX := hd.isProperVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety k (g ≫ sX) := hY
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hbir
  have hnY : topologicalKrullDim Y = n := hdim.symm.trans hn
  have hC := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  have e := hH'.divisorialSheafIso (hBc := hd.isCartier_H)
  have hI := intersectionNumberOn_eq_of_iso_pullback (sX := sX) hbir hn hnY hd.isCartier_H (hC H') e
  have hpos := hI ▸ intersectionNumberOn_pos_of_isNef_of_isBig (g ≫ sX) hnY (hC H')
    (isNef_of_iso_pullback hd.isNef_H (hC H') e)
    (isBig_of_isPullback hdim hd.isCartier_H (hC H') hH' hd.isBig_H)
  have hcoeff : ∀ P : MvPolynomial (Fin 2) ℚ, (∀ u : Fin 2 → ℤ,
      MvPolynomial.eval (fun i => (u i : ℚ)) P =
        Divisor.eulerPolynomial k (g ≫ sX) ![H', B'] A u) →
      P.coeff (Finsupp.single 0 n) =
        (Divisor.intersectionNumberOn k sX (𝟙 X) n hn.le (fun _ => H)
          (fun _ => hd.isCartier_H) : ℚ) / n.factorial := fun P hP => by
    rw [coeff_single_zero_eq_eval_homogeneousComponent,
      Divisor.eval_homogeneousComponent_of_eulerPolynomial k (g ≫ sX) hY hsm hnY ![H', B']
        (fun _ => hC _) A P hP, ← hI]
    congr 3
    exact funext fun _ => by simp [Fin.sum_univ_two]
  obtain ⟨P, -, hP⟩ := Divisor.exists_totalDegree_le_eval_eq_eulerPolynomial k (g ≫ sX) hsm
    hnY ![H', B'] A
  refine ⟨⟨P, fun h0 => ?_, hP⟩, hcoeff, hpos⟩
  have h := hcoeff P hP
  rw [h0, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, eq_comm, div_eq_zero_iff] at h
  exact h.elim (fun h => hpos.ne' (by exact_mod_cast h))
    (fun h => n.factorial_ne_zero (by exact_mod_cast h))

end MMP.Mori
