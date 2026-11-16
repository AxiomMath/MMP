module

public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# The local equation of `K_{X'/X}` is the Jacobian determinant (Lazarsfeld §9.1.B)

Let `μ : X' ⟶ X` be a birational morphism of non-singular varieties of dimension `n` over `k`,
`y ∈ X'`, `x = μ(y)`, `z₁, …, zₙ` a regular system of parameters of `𝒪_{X',y}` and `w₁, …, wₙ`
one of `𝒪_{X,x}`. Then `dz₁ ∧ ⋯ ∧ dzₙ` is a basis of `Ω^n_{X',y} = ⋀ⁿ Ω_{𝒪_{X',y}/k}`, so there
is a unique `J ∈ 𝒪_{X',y}` with `d(μ^♯w₁) ∧ ⋯ ∧ d(μ^♯wₙ) = J · dz₁ ∧ ⋯ ∧ dzₙ`; and `J` is a local
equation of `K_{X'/X}` at `y`.

## Main results

* `MMP.Intersection.IsRelativeCanonicalDivisor.existsUnique_jacobian`: existence and uniqueness
  of the Jacobian determinant `J`.
* `MMP.Intersection.IsRelativeCanonicalDivisor.isLocalEquationAt_jacobian`: `J` is a local
  equation of `K_{X'/X}` at `y`.

## Implementation notes

* `Ω^n_{X',y}` is `⋀ⁿ Ω[𝒪_{X',y} ⁄ 𝒪_{Spec k, ·}]` (through
  `Stacks.RelativeDifferentialStalkMap.formsStalkEquiv`); the stalk of `Spec k` at any point is
  `k`, so this is `⋀ⁿ Ω_{𝒪_{X',y}/k}`.
* Properness of `μ` (in Lazarsfeld's hypotheses) is not used: the statement is local at `y`.
* `k` is assumed perfect (Lazarsfeld works over `ℂ`). Over an imperfect field the statements fail:
  on `𝔸¹` over `𝔽_p(t)` at the point `x^p = t`, the regular parameter `z = x^p - t` has `dz = 0`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.RelativeDifferentialStalkMap

namespace MMP.Intersection

variable {k : Type u} [Field k] [PerfectField k] {X X' : Scheme.{u}}
variable [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

omit [PerfectField k] in
/-- On a smooth variety `Y` of dimension `n` over a field, the stalk `Ω_{𝒪_{Y,y}/𝒪_{Spec k,·}}`
of the relative differentials has rank `n`. -/
theorem finrank_kaehlerDifferential_stalk_of_isVariety {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k f] [Smooth f] {n : ℕ} (hn : topologicalKrullDim Y = n) (y : Y) :
    letI := algebraStalkMap f y
    Module.finrank (ToType (Y.sheaf.presheaf.stalk y))
      Ω[ToType (Y.sheaf.presheaf.stalk y)⁄ToType ((Spec (.of k)).presheaf.stalk (f y))] = n := by
  let := algebraStalkMap f y
  classical
  have heq : (f ⁻¹' {f y}) = (Set.univ : Set Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hdim : topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = n := by
    rwa [topologicalKrullDimAt_eq_of_homeomorph ((f.fiberHomeo (f y)).trans
        ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ Y))),
      ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y f]
  have hrank := AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt f y
  rw [hdim] at hrank
  rw [← (relativeDifferentialsStalkKaehlerEquiv f y).finrank_eq]
  exact_mod_cast hrank

/-- On a smooth variety `Y` of dimension `n` over a perfect field `k`, for a regular system of
parameters `z₁, …, zₙ` of `𝒪_{Y,y}`, the module `⋀ⁿ Ω_{𝒪_{Y,y}/k}` is free of rank one on
`dz₁ ∧ ⋯ ∧ dzₙ`. -/
theorem bijective_smul_ιMulti_D_stalk_of_isVariety {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k f] [Smooth f] {n : ℕ} (hn : topologicalKrullDim Y = n) (y : Y)
    {z : Fin n → Y.presheaf.stalk y} (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    letI := algebraStalkMap f y
    Function.Bijective fun r : ToType (Y.sheaf.presheaf.stalk y) =>
      r • exteriorPower.ιMulti (ToType (Y.sheaf.presheaf.stalk y)) n (fun i =>
        KaehlerDifferential.D (ToType ((Spec (.of k)).presheaf.stalk (f y)))
          (ToType (Y.sheaf.presheaf.stalk y)) (z i)) := by
  let := algebraStalkMap f y
  have : LocallyOfFiniteType f := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing (ToType (Y.sheaf.presheaf.stalk y)) :=
    inferInstanceAs (IsNoetherianRing (Y.presheaf.stalk y))
  have : IsLocalRing (ToType (Y.sheaf.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalRing (Y.presheaf.stalk y))
  have : Algebra.FormallySmooth (ToType ((Spec (.of k)).presheaf.stalk (f y)))
      (ToType (Y.sheaf.presheaf.stalk y)) :=
    InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f y
      (InfinitesimalLifting.smoothAt_of_smooth f y)
  have : Algebra.EssFiniteType (ToType ((Spec (.of k)).presheaf.stalk (f y)))
      (ToType (Y.sheaf.presheaf.stalk y)) := essFiniteType_stalkMap f y
  have : Algebra.FormallySmooth (ToType ((Spec (.of k)).presheaf.stalk (f y)))
      (IsLocalRing.ResidueField (ToType (Y.sheaf.presheaf.stalk y))) := by
    let : Field (ToType ((Spec (.of k)).presheaf.stalk (f y))) :=
      (isField_stalk_Spec_field k (f y)).toField
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f y)) := StructureSheaf.stalkAlgebra k (f y)
    have hsurj : Function.Surjective (algebraMap k ((Spec (.of k)).presheaf.stalk (f y))) :=
      fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)
    have : Algebra.IsAlgebraic k ((Spec (.of k)).presheaf.stalk (f y)) := ⟨fun r => by
      obtain ⟨a, rfl⟩ := hsurj r
      exact isAlgebraic_algebraMap a⟩
    have : PerfectField (ToType ((Spec (.of k)).presheaf.stalk (f y))) :=
      Algebra.IsAlgebraic.perfectField k
    have : Algebra.EssFiniteType (ToType (Y.sheaf.presheaf.stalk y))
        (IsLocalRing.ResidueField (ToType (Y.sheaf.presheaf.stalk y))) :=
      (RingHom.essFiniteType_algebraMap).mp
        (RingHom.FiniteType.of_surjective (algebraMap (ToType (Y.sheaf.presheaf.stalk y))
          (IsLocalRing.ResidueField (ToType (Y.sheaf.presheaf.stalk y))))
          IsLocalRing.residue_surjective).essFiniteType
    have : Algebra.EssFiniteType (ToType ((Spec (.of k)).presheaf.stalk (f y)))
        (IsLocalRing.ResidueField (ToType (Y.sheaf.presheaf.stalk y))) :=
      .comp _ (ToType (Y.sheaf.presheaf.stalk y)) _
    exact Algebra.FormallySmooth.of_perfectField
  exact bijective_smul_ιMulti_D_of_isRegularSystemOfParameters
    (finrank_kaehlerDifferential_stalk_of_isVariety f hn y) hz

omit [X.Over (Spec (.of k))] in
/-- **Lazarsfeld §9.1.B, the Jacobian determinant.** Let `μ : X' ⟶ X` be a morphism of
non-singular varieties of dimension `n` over `k`, `y ∈ X'`, `z₁, …, zₙ` a regular system of
parameters at `y` and `w₁, …, wₙ ∈ 𝒪_{X,μ(y)}`. Then there is a unique `J ∈ 𝒪_{X',y}` with
`d(μ^♯w₁) ∧ ⋯ ∧ d(μ^♯wₙ) = J · dz₁ ∧ ⋯ ∧ dzₙ` in `⋀ⁿ Ω_{𝒪_{X',y}/k}`. -/
@[mmp "lem_p09a_relative_canonical_divisor_local_equation"]
theorem existsUnique_jacobian
    [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))]
    (hsmX' : MMP.Mori.IsSmoothScheme (X' ↘ Spec (.of k))) (μ : X' ⟶ X) {n : ℕ}
    (hn : Scheme.dimension X' = n) (y : X') {z : Fin n → X'.presheaf.stalk y}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (w : Fin n → X.presheaf.stalk (μ y)) :
    letI := algebraStalkMap (X' ↘ Spec (.of k)) y
    ∃! J : ToType (X'.sheaf.presheaf.stalk y),
      exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i => KaehlerDifferential.D
          (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (μ.stalkMap y (w i))) =
        J • exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i =>
          KaehlerDifferential.D (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (z i)) := by
  let := algebraStalkMap (X' ↘ Spec (.of k)) y
  have : LocallyOfFiniteType (X' ↘ Spec (.of k)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (X' ↘ Spec (.of k)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth (X' ↘ Spec (.of k)) := (MMP.Mori.isSmoothScheme_iff _).mp hsmX'
  have hb := bijective_smul_ιMulti_D_stalk_of_isVariety (X' ↘ Spec (.of k)) hn y hz
  obtain ⟨J, hJ⟩ := hb.2 (exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n
    fun i => KaehlerDifferential.D (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y)))
      (ToType (X'.sheaf.presheaf.stalk y)) (μ.stalkMap y (w i)))
  exact ⟨J, hJ.symm, fun J' hJ' => hb.1 (hJ'.symm.trans hJ.symm)⟩

/-- The identification `formsStalkEquiv` of the stalk of `Ω^n_{X/S}` is semilinear on germs. -/
theorem formsStalkEquiv_germ_smul {S Y : Scheme.{u}} (f : Y ⟶ S) {U : Y.Opens} {x : Y}
    (hx : x ∈ U) (n : ℕ) (r : Γ(Y, U))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), U)) :
    letI := algebraStalkMap f x
    formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf U x hx (r • ω)) =
      Y.sheaf.presheaf.germ U x hx r • formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf U x hx ω) := by
  let := algebraStalkMap f x
  rw [← map_smul]
  congr 1
  exact PresheafOfModules.germ_smul (R := Y.presheaf)
    ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece (n : ℤ)).val x U hx r ω

omit [PerfectField k] [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] in
/-- The Jacobian section carries the pull-back of `dg₁ ∧ ⋯ ∧ dgₙ` to
`d(μ^♯g₁) ∧ ⋯ ∧ d(μ^♯gₙ)`. -/
theorem jacobianSection_app_pullbackUnit_gen (sX : X ⟶ Spec (.of k)) (μ : X' ⟶ X) (n : ℕ)
    (V : X.Opens) (g : Fin n → Γ(X, V)) :
    (jacobianSection sX μ n).app (μ ⁻¹ᵁ V)
        (Stacks.RingedSpace.pullbackUnit μ.toLRSHom.toShHom
          (Scheme.Hom.relativeDifferentialForms sX n) (Opposite.op V)
          (Stacks.DeRham.FormsGenerators.gen sX V g)) =
      Stacks.DeRham.FormsGenerators.gen (μ ≫ sX) (μ ⁻¹ᵁ V) fun i => μ.app V (g i) := by
  have h := congrArg (fun φ => φ.val.app (Opposite.op V) (Stacks.DeRham.FormsGenerators.gen sX V g))
    (Scheme.Hom.homEquiv_relativeDifferentialFormsMap μ sX (μ ≫ sX) (𝟙 _) (by simp) n)
  simp only at h
  exact h.trans (Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft μ sX (μ ≫ sX) (𝟙 _) _
    (Opposite.op V) n g)

/-- Finitely many germs at a point are germs of sections over a common neighbourhood. -/
theorem exists_germ_eq_of_fin {Y : Scheme.{u}} (y : Y) {n : ℕ} (w : Fin n → Y.presheaf.stalk y) :
    ∃ (V : Y.Opens) (hy : y ∈ V) (g : Fin n → Γ(Y, V)),
      ∀ i, Y.presheaf.germ V y hy (g i) = w i := by
  induction n with
  | zero => exact ⟨⊤, trivial, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨V, hy, g, hg⟩ := ih fun i => w i.succ
    obtain ⟨W, hyW, a, ha⟩ := Y.presheaf.exists_germ_eq (w 0)
    refine ⟨V ⊓ W, ⟨hy, hyW⟩, Fin.cons (Y.presheaf.map (homOfLE inf_le_right).op a)
      fun i => Y.presheaf.map (homOfLE inf_le_left).op (g i), fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ha
    · exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hg i)

/-- If `v` is a free generator and `v = c • ε`, then `c` is a unit and `ε = t • v` with
`c * t = 1`. -/
theorem exists_mul_eq_one_of_smul_eq {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {v ε : M} (hv : Function.Bijective fun r : A => r • v) {c : A} (h : v = c • ε) :
    ∃ t : A, ε = t • v ∧ c * t = 1 := by
  obtain ⟨t, ht⟩ := hv.2 ε
  have ht' : t • v = ε := ht
  refine ⟨t, ht'.symm, ?_⟩
  apply hv.1
  dsimp only
  rw [one_smul, mul_smul, ht', ← h]

/-- The bookkeeping of the Jacobian determinant: if `ι_w = J • ι_z`, `ι_w = g • ε₁`,
`ε₁ = r • ε` and `ε = t • ι_z`, with `ι_z` a free generator, then `J = r * (g * t)`. -/
theorem eq_mul_of_smul_chain {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {ιz ιw ε ε₁ : M} (hb : Function.Bijective fun r : A => r • ιz) {J g r t : A}
    (hJ : ιw = J • ιz) (hw : ιw = g • ε₁) (h1 : ε₁ = r • ε) (hε : ε = t • ιz) :
    J = r * (g * t) := by
  apply hb.1
  dsimp only
  rw [← hJ, hw, h1, hε, smul_smul, smul_smul]
  ring_nf

/-- If `c • a` is the generator `dg₁ ∧ ⋯ ∧ dgₙ` and the germs of the `gᵢ` at `x` are the `vᵢ`, then
`dv₁ ∧ ⋯ ∧ dvₙ` is the germ of `c` times the image of the germ of `a` in `⋀ⁿ Ω_{𝒪_{Y,x}}`. -/
theorem ιMulti_D_eq_germ_smul_formsStalkEquiv {S Y : Scheme.{u}} (f : Y ⟶ S) {U : Y.Opens}
    {x : Y} (hx : x ∈ U) {n : ℕ} {g : Fin n → Γ(Y, U)} {c : Γ(Y, U)}
    {a : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), U)}
    (h : c • a = Stacks.DeRham.FormsGenerators.gen f U g) {v : Fin n → Y.presheaf.stalk x}
    (hv : ∀ i, Y.presheaf.germ U x hx (g i) = v i) :
    letI := algebraStalkMap f x
    exteriorPower.ιMulti (ToType (Y.sheaf.presheaf.stalk x)) n (fun i =>
        KaehlerDifferential.D (ToType (S.presheaf.stalk (f x)))
          (ToType (Y.sheaf.presheaf.stalk x)) (v i)) =
      Y.sheaf.presheaf.germ U x hx c • formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf U x hx a) := by
  let := algebraStalkMap f x
  have h1 := formsStalkEquiv_germ_smul f hx n c a
  rw [h, formsStalkEquiv_germ_gen f hx g] at h1
  rw [← h1]
  exact congrArg _ (funext fun i => by rw [hv i])

/-- If `r • a` is the restriction of `s` to `U ⊆ W`, then at `x ∈ U` the image of the germ of `s`
in `⋀ⁿ Ω_{𝒪_{Y,x}}` is the germ of `r` times that of `a`. -/
theorem formsStalkEquiv_germ_eq_smul_of_le {S Y : Scheme.{u}} (f : Y ⟶ S) {n : ℕ}
    {U W : Y.Opens} (hUW : U ≤ W) {x : Y} (hx : x ∈ U)
    {s : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), W)} {r : Γ(Y, U)}
    {a : Γ(Scheme.Hom.relativeDifferentialForms f (n : ℤ), U)}
    (h : r • a = (Scheme.Hom.relativeDifferentialForms f n).presheaf.map (homOfLE hUW).op s) :
    letI := algebraStalkMap f x
    formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf W x (hUW hx) s) =
      Y.sheaf.presheaf.germ U x hx r • formsStalkEquiv f n x
        (TopCat.Presheaf.germ ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece
          (n : ℤ)).val.presheaf U x hx a) := by
  let := algebraStalkMap f x
  rw [← formsStalkEquiv_germ_smul f hx n r a, h]
  exact congrArg (formsStalkEquiv f n x) (TopCat.Presheaf.germ_res_apply
    ((Scheme.Hom.relativeDifferentials f).exteriorAlgebra.piece (n : ℤ)).val.presheaf
    (homOfLE hUW) x hx s).symm

open Stacks.DeRham.FormsGenerators in
/-- On a smooth variety of dimension `n`, a regular system of parameters `w` at `x` lifts to
sections `w̃` over a trivializing open `V` of `Ω^n` with generator `s₀`, and
`dw̃₁ ∧ ⋯ ∧ dw̃ₙ = d • s₀` for a section `d` whose germ at `x` is a unit. -/
theorem exists_isTrivializingGenerator_gen_eq_smul {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k f] [Smooth f] {n : ℕ} (hn : topologicalKrullDim Y = n)
    [Stacks.Ample.IsInvertibleModule Y (Scheme.Hom.relativeDifferentialForms f n)] (x : Y)
    {w : Fin n → Y.presheaf.stalk x} (hw : MMP.Mori.IsRegularSystemOfParameters w) :
    ∃ (V : Y.Opens) (hx : x ∈ V) (wt : Fin n → Γ(Y, V))
      (s₀ : Γ(Scheme.Hom.relativeDifferentialForms f n, V)) (d : Γ(Y, V)),
      (∀ i, Y.presheaf.germ V x hx (wt i) = w i) ∧
      IsTrivializingGenerator (Scheme.Hom.relativeDifferentialForms f n) V s₀ ∧
      d • s₀ = gen f V wt ∧ IsUnit (Y.presheaf.germ V x hx d) := by
  obtain ⟨V₀, hxV₀, wt₀, hwt₀⟩ := exists_germ_eq_of_fin x w
  obtain ⟨V, hVV₀, s₀, hxV, hs₀⟩ :=
    exists_isTrivializingGenerator (Scheme.Hom.relativeDifferentialForms f n) hxV₀
  have hwt : ∀ i, Y.presheaf.germ V x hxV (Y.presheaf.map (homOfLE hVV₀).op (wt₀ i)) = w i :=
    fun i => (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hwt₀ i)
  obtain ⟨d, (hd : d • s₀ = _)⟩ :=
    hs₀.bijective.2 (gen f V fun i => Y.presheaf.map (homOfLE hVV₀).op (wt₀ i))
  obtain ⟨t, -, ht⟩ := exists_mul_eq_one_of_smul_eq
    (bijective_smul_ιMulti_D_stalk_of_isVariety f hn x hw)
    (ιMulti_D_eq_germ_smul_formsStalkEquiv f hxV hd hwt)
  exact ⟨V, hxV, _, s₀, d, hwt, hs₀, hd, .of_mul_eq_one _ ht⟩

omit [PerfectField k] [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] in
open Stacks.DeRham.FormsGenerators in
/-- If `d • s₀ = dw₁ ∧ ⋯ ∧ dwₙ`, the Jacobian section carries `μ^♯d` times the pull-back of `s₀`
to `d(μ^♯w₁) ∧ ⋯ ∧ d(μ^♯wₙ)`. -/
theorem smul_jacobianSection_app_pullbackUnit (sX : X ⟶ Spec (.of k)) (μ : X' ⟶ X) {n : ℕ}
    {V : X.Opens} {d : Γ(X, V)} {s₀ : Γ(Scheme.Hom.relativeDifferentialForms sX n, V)}
    {wt : Fin n → Γ(X, V)} (hd : d • s₀ = gen sX V wt) :
    μ.app V d • (jacobianSection sX μ n).app (μ ⁻¹ᵁ V)
        (Stacks.RingedSpace.pullbackUnit μ.toLRSHom.toShHom
          (Scheme.Hom.relativeDifferentialForms sX n) (Opposite.op V) s₀) =
      gen (μ ≫ sX) (μ ⁻¹ᵁ V) fun i => μ.app V (wt i) := by
  have hu := Stacks.RingedSpace.pullbackUnit_smul μ.toLRSHom.toShHom
    (Scheme.Hom.relativeDifferentialForms sX n) (Opposite.op V) d s₀
  rw [← jacobianSection_app_pullbackUnit_gen, ← hd]
  exact (Scheme.Modules.Hom.app_smul _ (μ.app V d) _).symm.trans
    (congrArg ((jacobianSection sX μ n).app (μ ⁻¹ᵁ V)) hu).symm

/-- Multiplying a local equation `r` at `y` by a unit `u` of `𝒪_{Y,y}` gives a local equation. -/
theorem IsLocalEquationAt.stalkToTotalQuotient_mul_of_isUnit {Y : Scheme.{u}}
    {K : Y.CartierDivisor} {y : Y} {r u : Y.presheaf.stalk y}
    (hr : IsLocalEquationAt K y (stalkToTotalQuotient y r)) (hu : IsUnit u) :
    IsLocalEquationAt K y (stalkToTotalQuotient y (r * u)) := by
  simpa only [IsUnit.unit_spec, map_mul] using hr.mul_units hu.unit

omit [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))] in
open Stacks.DeRham.FormsGenerators in
/-- **The Jacobian determinant is a local equation of the divisor of the Jacobian section**, for
`μ : X' ⟶ X` a morphism of smooth varieties of dimension `n` over a perfect field, written with
the structure morphism `μ ≫ s_X` of `X'`. -/
theorem isLocalEquationAt_of_isDivisorOfHom_jacobianSection (sX : X ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sX] [Smooth sX] {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)]
    [Smooth (μ ≫ sX)] {n : ℕ} (hnX : topologicalKrullDim X = n)
    (hn : topologicalKrullDim X' = n) {K : X'.CartierDivisor}
    (hdiv : IsDivisorOfHom (jacobianSection sX μ n) K) (y : X')
    {z : Fin n → X'.presheaf.stalk y} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {w : Fin n → X.presheaf.stalk (μ y)} (hw : MMP.Mori.IsRegularSystemOfParameters w)
    (J : ToType (X'.sheaf.presheaf.stalk y))
    (hJ : letI := algebraStalkMap (μ ≫ sX) y
      exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i => KaehlerDifferential.D
          (ToType ((Spec (.of k)).presheaf.stalk ((μ ≫ sX) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (μ.stalkMap y (w i))) =
        J • exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i =>
          KaehlerDifferential.D (ToType ((Spec (.of k)).presheaf.stalk ((μ ≫ sX) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (z i))) :
    IsLocalEquationAt K y (stalkToTotalQuotient y J) := by
  let := algebraStalkMap (μ ≫ sX) y
  have hbY := bijective_smul_ιMulti_D_stalk_of_isVariety (μ ≫ sX) hn y hz
  have := smoothOfRelativeDimension_of_isVariety sX n hnX
  have := smoothOfRelativeDimension_of_isVariety (μ ≫ sX) n hn
  have hinvX := Stacks.Discriminant.isInvertible_relativeDifferentialForms sX n
  have hinvX' := Stacks.Discriminant.isInvertible_relativeDifferentialForms (μ ≫ sX) n
  have hLX := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := X.toRingedSpace)
    (Scheme.Hom.relativeDifferentialForms sX n) (h := hinvX)
  have : Stacks.Ample.IsInvertibleModule X (Scheme.Hom.relativeDifferentialForms sX n) := hinvX
  have : Stacks.Ample.IsInvertibleModule X'
      (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n) := hinvX'
  let φ := jacobianSection sX μ n
  let L := (Scheme.Modules.pullback μ).obj (Scheme.Hom.relativeDifferentialForms sX n)
  obtain ⟨V, hyV, wt, s₀, d, hwt, hs₀, hd', hdX⟩ :=
    exists_isTrivializingGenerator_gen_eq_smul sX hnX (μ y) hw
  let e₀ := Stacks.SheafOfModules.pullbackGenerator μ _ hLX V ⟨s₀, hs₀⟩
  have he₀ : IsTrivializingGenerator L (μ ⁻¹ᵁ V) e₀.val := e₀.2
  have hφ : μ.app V d • φ.app (μ ⁻¹ᵁ V) e₀.val = _ := smul_jacobianSection_app_pullbackUnit sX μ hd'
  obtain ⟨U₁, hyU₁, zt, hzt⟩ := exists_germ_eq_of_fin y z
  obtain ⟨U₂, hU₂, a, hyU₂, ha⟩ := exists_isTrivializingGenerator
    (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n) (V := μ ⁻¹ᵁ V ⊓ U₁) ⟨hyV, hyU₁⟩
  have h2V : U₂ ≤ μ ⁻¹ᵁ V := hU₂.trans inf_le_left
  have h21 : U₂ ≤ U₁ := hU₂.trans inf_le_right
  let e : Γ(L, U₂) := L.presheaf.map (homOfLE h2V).op e₀.val
  obtain ⟨r, (hr : r • a = φ.app U₂ e)⟩ := ha.bijective.2 (φ.app U₂ e)
  obtain ⟨hu, hloc⟩ := hdiv.2.2 U₂ e a (he₀.res h2V) ha r hr.symm
  obtain ⟨c, (hc : c • a = _)⟩ :=
    ha.bijective.2 (gen (μ ≫ sX) U₂ fun i => X'.presheaf.map (homOfLE h21).op (zt i))
  have hyV' : y ∈ μ ⁻¹ᵁ V := hyV
  obtain ⟨t, htε, hct⟩ := exists_mul_eq_one_of_smul_eq hbY
    (ιMulti_D_eq_germ_smul_formsStalkEquiv (μ ≫ sX) hyU₂ hc fun i =>
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans (hzt i))
  have hres : φ.app U₂ e = (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n).presheaf.map
      (homOfLE h2V).op (φ.app (μ ⁻¹ᵁ V) e₀.val) := by
    have hnat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h2V).op) e₀.val
    simp only [Scheme.Modules.mapPresheaf_app] at hnat
    exact hnat
  have hJeq := eq_mul_of_smul_chain hbY hJ
    (ιMulti_D_eq_germ_smul_formsStalkEquiv (μ ≫ sX) hyV' hφ fun i =>
      (Scheme.Hom.germ_stalkMap_apply μ V y hyV (wt i)).symm.trans (congrArg _ (hwt i)))
    (formsStalkEquiv_germ_eq_smul_of_le (μ ≫ sX) h2V hyU₂ (hr.trans hres)) htε
  have hgd : IsUnit (X'.sheaf.presheaf.germ (μ ⁻¹ᵁ V) y hyV' (μ.app V d)) :=
    (Scheme.Hom.germ_stalkMap_apply μ V y hyV d) ▸ hdX.map (μ.stalkMap y).hom
  have hloc' : IsLocalEquationAt K y (stalkToTotalQuotient y (X'.presheaf.germ U₂ y hyU₂ r)) :=
    ⟨U₂, hyU₂, hu.unit, hloc, by
      rw [IsUnit.unit_spec]
      exact germ_toTotalQuotient hyU₂ r⟩
  rw [hJeq]
  exact hloc'.stalkToTotalQuotient_mul_of_isUnit (hgd.mul (.of_mul_eq_one_right _ hct))

/-- **Lazarsfeld §9.1.B, the local equation of `K_{X'/X}`.** Let `μ : X' ⟶ X` be a birational
morphism of non-singular varieties of dimension `n` over `k`, `y ∈ X'`, `x = μ(y)`, `z₁, …, zₙ` a
regular system of parameters at `y` and `w₁, …, wₙ` one at `x`. If
`d(μ^♯w₁) ∧ ⋯ ∧ d(μ^♯wₙ) = J · dz₁ ∧ ⋯ ∧ dzₙ` in `⋀ⁿ Ω_{𝒪_{X',y}/k}`, then `J` is a local equation
of `K_{X'/X}` at `y`. -/
@[mmp "lem_p09a_relative_canonical_divisor_local_equation"]
theorem IsRelativeCanonicalDivisor.isLocalEquationAt_jacobian
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] (hsmX : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of k)))
    [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))]
    (hsmX' : MMP.Mori.IsSmoothScheme (X' ↘ Spec (.of k))) {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))]
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor (X ↘ Spec (.of k)) μ K) {n : ℕ}
    (hn : Scheme.dimension X' = n) (y : X') {z : Fin n → X'.presheaf.stalk y}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) {w : Fin n → X.presheaf.stalk (μ y)}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (J : ToType (X'.sheaf.presheaf.stalk y))
    (hJ : letI := algebraStalkMap (X' ↘ Spec (.of k)) y
      exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i => KaehlerDifferential.D
          (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (μ.stalkMap y (w i))) =
        J • exteriorPower.ιMulti (ToType (X'.sheaf.presheaf.stalk y)) n (fun i =>
          KaehlerDifferential.D (ToType ((Spec (.of k)).presheaf.stalk ((X' ↘ Spec (.of k)) y)))
          (ToType (X'.sheaf.presheaf.stalk y)) (z i))) :
    IsLocalEquationAt K y (stalkToTotalQuotient y J) := by
  have e : μ ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := CategoryTheory.comp_over μ _
  obtain ⟨n', hn', hdiv⟩ := hK.exists_isDivisorOfHom _ hμ
  obtain rfl : n' = n := by exact_mod_cast hn'.symm.trans hn
  have hdimX := (topologicalKrullDim_eq_of_isBirationalMorphism (X ↘ Spec (.of k))
    (X' ↘ Spec (.of k)) hμ).trans hn
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (X ↘ Spec (.of k)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth (X ↘ Spec (.of k)) := (MMP.Mori.isSmoothScheme_iff _).mp hsmX
  have : LocallyOfFiniteType (X' ↘ Spec (.of k)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (X' ↘ Spec (.of k)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hsm' : Smooth (X' ↘ Spec (.of k)) := (MMP.Mori.isSmoothScheme_iff _).mp hsmX'
  have hvar' : MMP.Mori.IsVariety k (X' ↘ Spec (.of k)) := inferInstance
  rw [← e] at hsm' hvar' hJ
  exact isLocalEquationAt_of_isDivisorOfHom_jacobianSection (X ↘ Spec (.of k)) hdimX hn hdiv y
    hz hw J hJ

end MMP.Intersection
