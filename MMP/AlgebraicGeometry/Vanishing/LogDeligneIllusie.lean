module
public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingCocycles
public import MMP.Topology.Sheaves.Godement
import MMP.Topology.Sheaves.GodementFlasqueResolution
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor

/-!
# The Deligne–Illusie decomposition and degeneration for a lifted simple normal crossing pair

Let `k` be a perfect field of characteristic `p`, let `V` be a smooth proper `k`-scheme of
relative dimension `n < p`, and let `S = ∑ⱼ Sⱼ` be a simple normal crossing divisor on `V`.
Suppose the pair `(V, S)` lifts to a smooth scheme `𝒱` over `W₂(k)` together with a relative
simple normal crossing divisor `𝒮 = ∑ⱼ 𝒮ⱼ` restricting to `S`. Then the Frobenius pushforward
`F_*Ω^•_{V/k}(log S)` of the logarithmic de Rham complex decomposes in the derived category of
`𝒪`-modules as the direct sum of its cohomology sheaves `Ω^i(log S)[-i]`, `0 ≤ i ≤ n`. In
particular the logarithmic Hodge-to-de Rham spectral
sequence `E₁^{i,q} = H^q(V, Ω^i_{V/k}(log S)) ⇒ ℍ^{i+q}(V, Ω^•_{V/k}(log S))` degenerates at
`E₁`.

## Main results

* `MMP.DeRham.nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift`:
  the decomposition
  `⨁_{i ≤ n} Ω^i_{V/k}(log S)[-i] ≅ F_*Ω^•_{V/k}(log S)`, and the `E₁`-degeneration of the
  logarithmic Hodge-to-de Rham spectral sequence.
* `MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField`: for an `𝒪_X`-module `M`
  on a `k`-scheme, Godement cohomology `H^q(X, M)` is additively isomorphic to the derived
  functor cohomology `cohomologyOverField k f M q`, compatibly with the action of `k`.

## Implementation notes

*Frobenius twist.* The source states the decomposition on the Frobenius twist `V^{(1)}`, for the
relative Frobenius `V → V^{(1)}`. Because `k` is perfect, the projection `V^{(1)} → V` is an
isomorphism of schemes; it carries `S^{(1)}` to `S` and `Ω^i_{V^{(1)}/k}(log S^{(1)})` to
`Ω^i_{V/k}(log S)`, and composed with the relative Frobenius it is the absolute Frobenius `F` of
`V`. So the statement is made in the derived category of `𝒪_V`-modules, with
`F_* = Scheme.Modules.pushforward (absoluteFrobenius V p hV)`, where `a ∈ 𝒪_V` acts by `aᵖ`.

*Simple normal crossings.* The components are given by ideal sheaves `Jⱼ` on `V` and `Iⱼ` on `𝒱`.
The divisor is simple normal crossing when, for every finite set `T` of components, the
intersection `⋂_{j ∈ T}` (the subscheme of `⨆_{j ∈ T}`) is smooth of relative dimension
`n - #T`, and empty when `#T > n`; the case `T = ∅` is the smoothness of the ambient scheme.
The lift is a pullback square exhibiting `V` as the closed fibre of `𝒱 → Spec W₂(k)` along
`π : W₂(k) → k`, the zeroth Witt coordinate, with each `Sⱼ` the preimage of `𝒮ⱼ`. The map `π`
is a parameter pinned by `hπ`, since a ring homomorphism cannot be written inside a statement.

*The logarithmic de Rham complex.* Its terms enter as `𝒪_V`-modules `K q` with injective,
`𝒪_V`-linear maps `e`, natural in the open `W`, from `Γ(K q, W)` to the `q`-forms on `W ∩ U`,
`U = V ∖ S`. Their image is cut out by Deligne's criterion: a form `ω` on `W ∩ U` is
logarithmic exactly when `fω` and `f dω` extend over every affine `W' ⊆ W`, for every product
`f = ∏ⱼ cⱼ` of sections `cⱼ` of the ideals `Jⱼ` over `W'`. This determines `K q` up to unique
isomorphism as the subsheaf `Ω^q_{V/k}(log S)` of `j_*Ω^q_{U/k}`. The differential `d` of
`F_*K^•` is a morphism of `𝒪_V`-modules determined by its compatibility with the de Rham
differential, the arrows of `Scheme.Hom.deRhamComplex`.

*Degeneration at `E₁`.* The Hodge-to-de Rham spectral sequence is the spectral sequence of the
stupid filtration `σ^{≥i}Ω^•` of the de Rham complex, a complex of abelian sheaves whose
hypercohomology is computed by the Godement resolution, `MMP.Analytic.hypercohomology`. For a
finite filtration, degeneration at `E₁` is equivalent to the injectivity of every map
`ℍ^m(V, σ^{≥i}Ω^•) ⟶ ℍ^m(V, Ω^•)` ([Deligne1971], 1.3.2), and this is the form stated. The
truncation enters through its characterising property: any complex `L` vanishing in degrees
`< i` with a map `φ : L ⟶ Ω^•` that is an isomorphism in degrees `≥ i`. The complex is taken in
the form `F_*Ω^•_{V/k}(log S)`: the absolute Frobenius is the identity on the underlying space
of `V`, so its underlying complex of abelian sheaves is that of `Ω^•_{V/k}(log S)`.

*Proof.* The decomposition `⨁_{q ≤ n} Ω^q(log S)[-q] ≅ F_*Ω^•(log S)` is
`MMP.DeRham.FrobeniusSplittingData.nonempty_iso_directSum_singleFunctor`.

Degeneration at `E₁` is read off from dimensions. Write `A_i^m = ℍ^m(σ^{≥i}F_*Ω^•)` and
`E_i^m = ℍ^m(F_*Ω^i[-i])` for the Godement hypercohomology of the underlying complexes of
abelian sheaves. The field `k` acts on all of them through `Γ(V, 𝒪_V)`, and every map induced by a
morphism of complexes of `𝒪_V`-modules, as well as every connecting map, is `k`-linear. The
degreewise split short exact sequences `σ^{≥i+1} → σ^{≥i} → F_*Ω^i[-i]` give long exact sequences
`A_{i+1}^m → A_i^m → E_i^m → A_{i+1}^{m+1}`. When all of these spaces are finite-dimensional and
`dim A_0^m = ∑_i dim E_i^m`, every connecting map vanishes and every `A_{i+1}^m → A_i^m` is
injective; a complex `L` vanishing below `i` with a map to `F_*Ω^•` that is an isomorphism from
degree `i` on is `σ^{≥i}F_*Ω^•`.

The two inputs come from the following facts.

* The Čech cocycles of the decomposition are morphisms of complexes `Ω^q[-q] ⟶ Tot Č(F_*Ω^•)`,
  and their sum `⨁_q Ω^q[-q] ⟶ Tot Č(F_*Ω^•)` is a quasi-isomorphism, as is the Čech resolution
  `F_*Ω^• ⟶ Tot Č(F_*Ω^•)`. Hypercohomology inverts quasi-isomorphisms of complexes concentrated
  in nonnegative degrees and commutes with finite biproducts, so
  `dim ℍ^m(F_*Ω^•) = ∑_q dim ℍ^m(Ω^q[-q])`.
* The underlying abelian sheaf of `F_*M` is that of `M`, with `c ∈ k` acting by `c ^ p`, so
  `ℍ^m(F_*Ω^q[-q])` and `ℍ^m(Ω^q[-q])` have the same dimension, `k` being perfect.
* `ℍ^m(M[-q]) ≅ ℍ^{m-q}(M)` (hypercohomology commutes with shifts), and for an `𝒪_V`-module `M`
  the Godement cohomology of the underlying abelian sheaf is its derived functor cohomology as an
  `𝒪_V`-module ([Stacks 03FD]), compatibly with the action of `Γ(V, 𝒪_V)`. For `M` coherent and
  `V` proper this is finite-dimensional over `k`.
* The sheaves `Ω^q(log S)` are coherent: on a chart of the divisor their sections are the
  logarithmic forms, a finitely generated module whose localizations at basic opens are the
  logarithmic forms there (Deligne's criterion).

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], Théorème 2.1, Corollaire 2.4 and §4.2.
* [P. Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971)][Deligne1971], 1.3.2, 3.1.
* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992], §10.
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

namespace MMP.DeRham

universe u

/-! ### Godement hypercohomology inverts quasi-isomorphisms -/

section GodementQuasiIso

open ZeroObject TopCat TopologicalSpace MMP.Analytic MMP.Analytic.CokernelCoresolution

section Generic

variable {C : Type*} [Category C] [Abelian C]

/-- **Cokernels of a monomorphism of short exact sequences.** If `φ : S₁ ⟶ S₂` is a morphism of
short exact sequences with monomorphic components and `π : S₂ ⟶ L` is a cokernel of `φ` in each
component, then `L` is short exact. -/
private theorem shortExact_of_isColimit_cokernelCofork {S₁ S₂ L : ShortComplex C} (φ : S₁ ⟶ S₂)
    (π : S₂ ⟶ L) (hπ : φ ≫ π = 0) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (m₁ : Mono φ.τ₁) (m₂ : Mono φ.τ₂) (m₃ : Mono φ.τ₃)
    (c₁ : IsColimit (CokernelCofork.ofπ π.τ₁ (by rw [← ShortComplex.comp_τ₁, hπ]; rfl)))
    (c₂ : IsColimit (CokernelCofork.ofπ π.τ₂ (by rw [← ShortComplex.comp_τ₂, hπ]; rfl)))
    (c₃ : IsColimit (CokernelCofork.ofπ π.τ₃ (by rw [← ShortComplex.comp_τ₃, hπ]; rfl))) :
    L.ShortExact := by
  haveI := m₁
  haveI := m₂
  haveI := m₃
  haveI := h₂.epi_g
  have hZ : IsZero (ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)) := by
    rw [IsZero.iff_id_eq_zero]
    ext <;> exact (isZero_zero C).eq_of_src _ _
  haveI : Mono φ := by
    constructor
    intro Z a b h
    ext
    · exact (cancel_mono φ.τ₁).1 (by rw [← ShortComplex.comp_τ₁, h, ShortComplex.comp_τ₁])
    · exact (cancel_mono φ.τ₂).1 (by rw [← ShortComplex.comp_τ₂, h, ShortComplex.comp_τ₂])
    · exact (cancel_mono φ.τ₃).1 (by rw [← ShortComplex.comp_τ₃, h, ShortComplex.comp_τ₃])
  let SI : ShortComplex.SnakeInput C :=
    { L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)
      L₁ := S₁
      L₂ := S₂
      L₃ := L
      v₀₁ := 0
      v₁₂ := φ
      v₂₃ := π
      w₀₂ := by simp
      w₁₃ := hπ
      h₀ := KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance hZ
      h₃ := ShortComplex.isColimitOfIsColimitπ _
        ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ hπ).symm c₁)
        ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ hπ).symm c₂)
        ((isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ hπ).symm c₃)
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have : Epi SI.L₃.g := SI.epi_L₃_g
  have : Mono SI.L₃.f := SI.L₂'_exact.mono_g ((isZero_zero C).eq_of_src _ _)
  exact ⟨SI.L₃_exact⟩

/-- A cokernel of `e ≫ f` with `e` epi is a cokernel of `f`. -/
private def isColimitCokernelCoforkOfEpiComp {X Y Z W : C} (e : W ⟶ X) [Epi e] (f : X ⟶ Y)
    (p : Y ⟶ Z) (hp : (e ≫ f) ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p hp)) :
    IsColimit (CokernelCofork.ofπ p (by rw [← cancel_epi e, ← Category.assoc, hp, comp_zero]) :
      CokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ h.desc (CokernelCofork.ofπ g (by rw [Category.assoc, hg, comp_zero])))
    (fun g hg ↦ h.fac (CokernelCofork.ofπ g (by rw [Category.assoc, hg, comp_zero]))
      WalkingParallelPair.one)
    (fun g hg m hm ↦ Cofork.IsColimit.hom_ext h (by
      rw [Cofork.π_ofπ, hm]
      exact (h.fac (CokernelCofork.ofπ g (by rw [Category.assoc, hg, comp_zero]))
        WalkingParallelPair.one).symm))

variable (G : C ⥤ C) (η : 𝟭 C ⟶ G)

private lemma cokerDesc_comp_cokerDesc {F F' F'' : C} (a : F ⟶ F') (b : F' ⟶ F'') (n : ℕ) :
    cokerDesc (stageHom (idLift G η) a n) ≫ cokerDesc (stageHom (idLift G η) b n) =
      cokerDesc (stageHom (idLift G η) (a ≫ b) n) := by
  refine coequalizer.hom_ext ?_
  change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
  rw [π_cokerDesc_assoc, π_cokerDesc]
  change homX (idLift G η) a n ≫ cokernel.π (stage G η F' n).2.2 ≫
      cokerDesc (stageHom (idLift G η) b n) =
    homX (idLift G η) (a ≫ b) n ≫ cokernel.π (stage G η F'' n).2.2
  rw [π_cokerDesc, homX_comp, Category.assoc]
  rfl

private lemma cokerDesc_zero [G.PreservesZeroMorphisms] (F F' : C) (n : ℕ) :
    cokerDesc (stageHom (idLift G η) (0 : F ⟶ F') n) = 0 := by
  refine coequalizer.hom_ext ?_
  change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
  rw [π_cokerDesc, comp_zero]
  change homX (idLift G η) (0 : F ⟶ F') n ≫ cokernel.π (stage G η F' n).2.2 = 0
  rw [homX_zero_hom, zero_comp]

/-- The cokernels `coker(G^{n-1}(S) ⟶ G^n(S))` of the stages of the coresolutions of the terms of a
short complex `S`. -/
private noncomputable def cokernelStage [G.PreservesZeroMorphisms] (S : ShortComplex C) (n : ℕ) :
    ShortComplex C :=
  ShortComplex.mk (cokerDesc (stageHom (idLift G η) S.f n))
    (cokerDesc (stageHom (idLift G η) S.g n)) (by
      rw [cokerDesc_comp_cokerDesc, S.zero]
      exact cokerDesc_zero G η _ _ n)

/-- **The cokernel coresolution preserves short exact sequences** when `G` does and `η` is a
monomorphism. -/
private theorem shortExact_cokernelStage [G.PreservesZeroMorphisms] [∀ F, Mono (η.app F)]
    (hG : ∀ S : ShortComplex C, S.ShortExact → (S.map G).ShortExact)
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (cokernelStage G η S n).ShortExact := by
  induction n with
  | zero =>
    refine shortExact_of_isColimit_cokernelCofork
      (S₂ := S.map G)
      { τ₁ := η.app _, τ₂ := η.app _, τ₃ := η.app _
        comm₁₂ := (η.naturality S.f).symm, comm₂₃ := (η.naturality S.g).symm }
      { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _
        comm₁₂ := π_cokerDesc (stageHom (idLift G η) S.f 0)
        comm₂₃ := π_cokerDesc (stageHom (idLift G η) S.g 0) }
      (by ext <;> exact cokernel.condition _) hS (hG S hS) inferInstance inferInstance inferInstance
      (cokernelIsCokernel _) (cokernelIsCokernel _) (cokernelIsCokernel _)
  | succ n ih =>
    refine shortExact_of_isColimit_cokernelCofork
      (S₂ := (cokernelStage G η S n).map G)
      { τ₁ := η.app (cokernel (stage G η S.X₁ n).2.2)
        τ₂ := η.app (cokernel (stage G η S.X₂ n).2.2)
        τ₃ := η.app (cokernel (stage G η S.X₃ n).2.2)
        comm₁₂ := (η.naturality _).symm, comm₂₃ := (η.naturality _).symm }
      { τ₁ := cokernel.π _, τ₂ := cokernel.π _, τ₃ := cokernel.π _
        comm₁₂ := π_cokerDesc (stageHom (idLift G η) S.f (n + 1))
        comm₂₃ := π_cokerDesc (stageHom (idLift G η) S.g (n + 1)) }
      ?_ ih (hG _ ih) (‹∀ F, Mono (η.app F)› _) (‹∀ F, Mono (η.app F)› _)
      (‹∀ F, Mono (η.app F)› _)
      (isColimitCokernelCoforkOfEpiComp (cokernel.π (stage G η S.X₁ n).2.2) _ _
        (cokernel.condition (stage G η S.X₁ (n + 1)).2.2) (cokernelIsCokernel _))
      (isColimitCokernelCoforkOfEpiComp (cokernel.π (stage G η S.X₂ n).2.2) _ _
        (cokernel.condition (stage G η S.X₂ (n + 1)).2.2) (cokernelIsCokernel _))
      (isColimitCokernelCoforkOfEpiComp (cokernel.π (stage G η S.X₃ n).2.2) _ _
        (cokernel.condition (stage G η S.X₃ (n + 1)).2.2) (cokernelIsCokernel _))
    ext
    · exact (cancel_epi (cokernel.π (stage G η S.X₁ n).2.2)).1 ((Category.assoc _ _ _).symm.trans
        ((cokernel.condition (stage G η S.X₁ (n + 1)).2.2).trans comp_zero.symm))
    · exact (cancel_epi (cokernel.π (stage G η S.X₂ n).2.2)).1 ((Category.assoc _ _ _).symm.trans
        ((cokernel.condition (stage G η S.X₂ (n + 1)).2.2).trans comp_zero.symm))
    · exact (cancel_epi (cokernel.π (stage G η S.X₃ n).2.2)).1 ((Category.assoc _ _ _).symm.trans
        ((cokernel.condition (stage G η S.X₃ (n + 1)).2.2).trans comp_zero.symm))

end Generic

section Godement

variable {T : TopCat.{u}}

/-- A short complex of sheaves of abelian groups which is short exact on the sections over every
open set is short exact. -/
private theorem shortExact_of_sections (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T))
    (hf : ∀ U, Function.Injective (S.f.hom.app U))
    (hg : ∀ U, Function.Surjective (S.g.hom.app U))
    (hfg : ∀ U x₂, S.g.hom.app U x₂ = 0 → ∃ x₁, S.f.hom.app U x₁ = x₂) :
    S.ShortExact := by
  have hm : Mono S.f := by
    refine (Sheaf.forget AddCommGrpCat.{u} T).mono_of_mono_map ?_
    have : ∀ U, Mono ((Sheaf.forget AddCommGrpCat.{u} T).map S.f |>.app U) := fun U ↦
      (AddCommGrpCat.mono_iff_injective _).2 (hf U)
    exact NatTrans.mono_of_mono_app _
  have he : Epi S.g := by
    refine (Sheaf.forget AddCommGrpCat.{u} T).epi_of_epi_map ?_
    have : ∀ U, Epi ((Sheaf.forget AddCommGrpCat.{u} T).map S.g |>.app U) := fun U ↦
      (AddCommGrpCat.epi_iff_surjective _).2 (hg U)
    exact NatTrans.epi_of_epi_app _
  refine ⟨?_⟩
  rw [Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := Presheaf.germ_exist S.X₂.presheaf y
  change (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom (S.X₂.presheaf.germ U x hxU s) = 0
    at hy
  rw [Presheaf.stalkFunctor_map_germ_apply] at hy
  obtain ⟨W, hxW, iU, iV, hW⟩ := Presheaf.germ_eq S.X₃.presheaf x hxU hxU
    (S.g.hom.app (op U) s) 0 (hy.trans (map_zero _).symm)
  obtain ⟨t, ht⟩ := hfg (op W) (S.X₂.presheaf.map iU.op s) (by
    erw [NatTrans.naturality_apply S.g.hom iU.op s]
    exact hW.trans (map_zero _))
  refine ⟨S.X₁.presheaf.germ W x hxW t, ?_⟩
  change (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom (S.X₁.presheaf.germ W x hxW t) = _
  rw [Presheaf.stalkFunctor_map_germ_apply, ht, Presheaf.germ_res_apply]

/-- The stalks of a short exact sequence of sheaves of abelian groups are short exact. -/
private theorem stalk_shortExact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}
    (hS : S.ShortExact) (x : T) :
    Function.Injective ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom) ∧
      Function.Surjective ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom) ∧
      ∀ y, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.hom y = 0 →
        ∃ z, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.hom z = y := by
  have h := hS.map_of_exact
    (Sheaf.forget AddCommGrpCat.{u} T ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  exact ⟨(AddCommGrpCat.mono_iff_injective _).1 h.mono_f,
    (AddCommGrpCat.epi_iff_surjective _).1 h.epi_g, (ShortComplex.ab_exact_iff _).1 h.exact⟩

/-- The Godement sheaf of a short exact sequence is short exact on sections over every open. -/
private theorem godementFunctor_app_shortExact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}
    (hS : S.ShortExact) (U : (Opens T)ᵒᵖ) :
    Function.Injective (((godementFunctor T).map S.f).hom.app U) ∧
      Function.Surjective (((godementFunctor T).map S.g).hom.app U) ∧
      ∀ y, ((godementFunctor T).map S.g).hom.app U y = 0 →
        ∃ z, ((godementFunctor T).map S.f).hom.app U z = y := by
  have h := fun x : T ↦ stalk_shortExact hS x
  refine ⟨fun s t hst ↦ funext fun x ↦ (h x.1).1 (congrFun hst x), fun t ↦ ?_, fun t ht ↦ ?_⟩
  · choose s hs using fun x : U.unop ↦ (h x.1).2.1 (t x)
    exact ⟨s, funext hs⟩
  · choose s hs using fun x : U.unop ↦ (h x.1).2.2 (t x) (congrFun ht x)
    exact ⟨s, funext hs⟩

/-- The Godement functor preserves short exact sequences. -/
private theorem godementFunctor_shortExact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)}
    (hS : S.ShortExact) : (S.map (godementFunctor T)).ShortExact :=
  shortExact_of_sections _ (fun U ↦ (godementFunctor_app_shortExact hS U).1)
    (fun U ↦ (godementFunctor_app_shortExact hS U).2.1)
    (fun U ↦ (godementFunctor_app_shortExact hS U).2.2)

/-- The global sections of the Godement sheaf of a short exact sequence are short exact. -/
private theorem globalSections_godementFunctor_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact) :
    ((S.map (godementFunctor T)).map (globalSections T)).ShortExact := by
  obtain ⟨h₁, h₂, h₃⟩ := godementFunctor_app_shortExact hS (op ⊤)
  have : Mono ((S.map (godementFunctor T)).map (globalSections T)).f :=
    (AddCommGrpCat.mono_iff_injective _).2 h₁
  have : Epi ((S.map (godementFunctor T)).map (globalSections T)).g :=
    (AddCommGrpCat.epi_iff_surjective _).2 h₂
  exact ⟨(ShortComplex.ab_exact_iff _).2 h₃⟩

private theorem mono_godementUnit_app_of_injective (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    Mono ((godementUnit T).app F) := by
  refine (Sheaf.forget AddCommGrpCat.{u} T).mono_of_mono_map ?_
  have : ∀ U, Mono ((Sheaf.forget AddCommGrpCat.{u} T).map ((godementUnit T).app F) |>.app U) :=
    fun U ↦ (AddCommGrpCat.mono_iff_injective _).2 (godementUnit_app_hom_app_injective F U)
  exact NatTrans.mono_of_mono_app _

private theorem additive_godementFunctor : (godementFunctor T).Additive where
  map_add {F F'} {a b} := sheafHom_ext fun U s => funext fun x => by
    change (Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map (a.hom + b.hom) (s x) = _
    rw [Functor.map_add]
    rfl

end Godement

attribute [local instance] mono_godementUnit_app_of_injective additive_godementFunctor

section Additivity

variable {C : Type*} [Category C] [Preadditive C] [HasCokernels C] (G : C ⥤ C) (η : 𝟭 C ⟶ G)
  [G.Additive]

private lemma homX_add {F F' : C} (a b : F ⟶ F') (n : ℕ) :
    homX (idLift G η) (a + b) n = homX (idLift G η) a n + homX (idLift G η) b n := by
  induction n with
  | zero => exact G.map_add
  | succ n ih =>
    have e : cokerDesc (stageHom (idLift G η) (a + b) n) =
        cokerDesc (stageHom (idLift G η) a n) + cokerDesc (stageHom (idLift G η) b n) := by
      refine coequalizer.hom_ext ?_
      change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
      rw [Preadditive.comp_add, π_cokerDesc, π_cokerDesc, π_cokerDesc]
      change homX (idLift G η) (a + b) n ≫ cokernel.π (stage G η F' n).2.2 =
        homX (idLift G η) a n ≫ cokernel.π (stage G η F' n).2.2 +
          homX (idLift G η) b n ≫ cokernel.π (stage G η F' n).2.2
      rw [ih, Preadditive.add_comp]
    change G.map (cokerDesc (stageHom (idLift G η) (a + b) n)) =
      G.map (cokerDesc (stageHom (idLift G η) a n)) + G.map (cokerDesc (stageHom (idLift G η) b n))
    rw [e, G.map_add]

private theorem additive_complexFunctor : (complexFunctor G η).Additive where
  map_add {F F'} {a b} := by
    ext n
    exact homX_add G η a b n

end Additivity

attribute [local instance] additive_complexFunctor

section Hypercohomology

variable (T : TopCat.{u})

private theorem additive_globalSections : (globalSections T).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⋙
    (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).Additive

attribute [local instance] additive_globalSections

private theorem additive_godementResolution : (godementResolution T).Additive :=
  inferInstanceAs (complexFunctor (godementFunctor T) (godementUnit T)).Additive

attribute [local instance] additive_godementResolution

/-- **`F ↦ Γ(T, Gⁿ(F))` is exact.** -/
private theorem godementResolution_eval_globalSections_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (godementResolution T ⋙ HomologicalComplex.eval _ _ n ⋙
      globalSections T)).ShortExact := by
  cases n with
  | zero => exact globalSections_godementFunctor_shortExact hS
  | succ n =>
    exact globalSections_godementFunctor_shortExact (shortExact_cokernelStage (godementFunctor T)
      (godementUnit T) (fun S hS => godementFunctor_shortExact hS) hS n)

private theorem preservesHomology_godementResolution_eval_globalSections (n : ℕ) :
    (godementResolution T ⋙ HomologicalComplex.eval _ _ n ⋙ globalSections T).PreservesHomology :=
  ((godementResolution T ⋙ HomologicalComplex.eval _ _ n ⋙ globalSections T).exact_tfae.out 1 3).1
    fun _ hS => godementResolution_eval_globalSections_shortExact T hS n

attribute [local instance] preservesHomology_godementResolution_eval_globalSections

/-- The column of degree `m` of the Godement double complex is `Γ(T, Gᵐ(-))`. -/
private noncomputable def godementSectionsEvalIso (m : ℕ) :
    godementSections T ⋙ HomologicalComplex.eval _ _ (m : ℤ) ≅
      godementResolution T ⋙ HomologicalComplex.eval _ _ m ⋙ globalSections T :=
  NatIso.ofComponents
    (fun F => HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat rfl)
    (fun {F G} a => by
      change (HomologicalComplex.extendMap _ _).f _ ≫ _ = _
      rw [HomologicalComplex.extendMap_f _ _
        (show ComplexShape.embeddingUpNat.f m = (m : ℤ) from rfl)]
      simp
      rfl)

private lemma isZero_godementSections_X_of_neg (F : TopCat.Sheaf AddCommGrpCat.{u} T) {q : ℤ}
    (hq : q < 0) : IsZero (((godementSections T).obj F).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    change (i : ℤ) = q at hi
    omega)

/-- A morphism of double complexes induces a morphism of the flipped double complexes. -/
private def flipHom
    {Z Z' : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (Φ : Z ⟶ Z') : Z.flip ⟶ Z'.flip where
  f i := { f := fun j => (Φ.f j).f i
           comm' := fun j j' _ => HomologicalComplex.congr_hom (Φ.comm j j') i }
  comm' i i' _ := HomologicalComplex.hom_ext _ _ fun k => (Φ.f k).comm i i'

private lemma total_map_flip_comp_totalFlipIso
    {Z Z' : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (Φ : Z ⟶ Z') :
    HomologicalComplex₂.total.map (flipHom Φ)
        (ComplexShape.up ℤ) ≫ (Z'.totalFlipIso (ComplexShape.up ℤ)).hom =
      (Z.totalFlipIso (ComplexShape.up ℤ)).hom ≫
        HomologicalComplex₂.total.map Φ (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine HomologicalComplex₂.total.hom_ext (K := Z.flip) _ fun i₁ i₂ h => ?_
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc]
  erw [Linear.comp_units_smul, Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map]
  rfl

private lemma isZero_of_isZero_X {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} {K : HomologicalComplex C c} (h : ∀ i, IsZero (K.X i)) : IsZero K :=
  (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i => (h i).eq_of_src _ _)

private lemma quasiIso_of_isZero {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L) (hK : IsZero K)
    (hL : IsZero L) : QuasiIso f := by
  have : IsIso f := isIso_of_source_target_iso_zero f hK.isoZero hL.isoZero
  infer_instance

/-- **Hypercohomology inverts quasi-isomorphisms** between complexes concentrated in nonnegative
degrees. -/
private theorem isIso_hypercohomology_map
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (hK : ∀ p < 0, IsZero (K.X p)) (hL : ∀ p < 0, IsZero (L.X p))
    (n : ℤ) : IsIso ((hypercohomology T n).map φ) := by
  set Φ := ((godementSections T).mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  have hflip : QuasiIso (HomologicalComplex₂.total.map (flipHom Φ) (ComplexShape.up ℤ)) := by
    refine StacksDraft.TotalComplexQuasiIso.quasiIso_total_map (flipHom Φ) 0 ?_ ?_ ?_ ?_ ?_
    · intro p q hq
      exact (HomologicalComplex.eval _ _ p).map_isZero ((godementSections T).map_isZero (hK q hq))
    · intro p hp
      exact isZero_of_isZero_X fun q => isZero_godementSections_X_of_neg T _ hp
    · intro p q hq
      exact (HomologicalComplex.eval _ _ p).map_isZero ((godementSections T).map_isZero (hL q hq))
    · intro p hp
      exact isZero_of_isZero_X fun q => isZero_godementSections_X_of_neg T _ hp
    · intro p
      rcases lt_or_ge p 0 with hp | hp
      · exact quasiIso_of_isZero _
          (isZero_of_isZero_X fun q => isZero_godementSections_X_of_neg T _ hp)
          (isZero_of_isZero_X fun q => isZero_godementSections_X_of_neg T _ hp)
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
        let e := NatIso.mapHomologicalComplex (godementSectionsEvalIso T m) (ComplexShape.up ℤ)
        exact (quasiIso_iff_of_arrow_mk_iso _ _
          (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality φ).symm)).2
          (HomologicalComplex.quasiIso_map_of_preservesHomology φ
            (godementResolution T ⋙ HomologicalComplex.eval _ _ m ⋙ globalSections T))
  have hq : QuasiIso (HomologicalComplex₂.total.map Φ (ComplexShape.up ℤ)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (HomologicalComplex₂.totalFlipIso _ _)
      (HomologicalComplex₂.totalFlipIso _ _) (total_map_flip_comp_totalFlipIso Φ).symm)).1 hflip
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hq.quasiIsoAt n)

end Hypercohomology

end GodementQuasiIso

section Smul

variable {X : Scheme.{u}}

/-- Multiplication by a global function, as an endomorphism of an `𝒪_X`-module. -/
private noncomputable def smulHom (s : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun W => (M.smul (X.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op s)).asHom
      naturality := fun W₁ W₂ g => by
        ext x
        have h := Scheme.Modules.map_smul M g.unop
          (X.presheaf.map (homOfLE (le_top : W₁.unop ≤ ⊤)).op s) x
        have e : X.presheaf.map g.unop.op (X.presheaf.map (homOfLE (le_top : W₁.unop ≤ ⊤)).op s) =
            X.presheaf.map (homOfLE (le_top : W₂.unop ≤ ⊤)).op s := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          rfl
        rw [e] at h
        exact h.symm }
    (fun W r x => by
      have hc : ∀ a b : X.ringCatSheaf.obj.obj W, a * b = b * a := fun a b =>
        @mul_comm Γ(X, W.unop) _ a b
      exact (smul_smul _ r x).trans ((congrArg (· • x) (hc _ r)).trans (smul_smul r _ x).symm))⟩

private lemma smulHom_app (s : Γ(X, ⊤)) (M : X.Modules) (W : X.Opens) (x : Γ(M, W)) :
    (smulHom s M).app W x = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s • x := rfl

@[reassoc]
private lemma smulHom_naturality (s : Γ(X, ⊤)) {M N : X.Modules} (g : M ⟶ N) :
    smulHom s M ≫ g = g ≫ smulHom s N := by
  ext W x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app,
    Scheme.Modules.Hom.app_smul]

private lemma smulHom_mul (s t : Γ(X, ⊤)) (M : X.Modules) :
    smulHom (s * t) M = smulHom t M ≫ smulHom s M := by
  ext W x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app, map_mul,
    mul_smul]

private lemma smulHom_add (s t : Γ(X, ⊤)) (M : X.Modules) :
    smulHom (s + t) M = smulHom s M + smulHom t M := by
  ext W x
  simp only [Scheme.Modules.Hom.add_app, smulHom_app, map_add, add_smul]
  rfl

private lemma smulHom_one (M : X.Modules) : smulHom (1 : Γ(X, ⊤)) M = 𝟙 M := by
  ext W x
  simp only [smulHom_app, map_one, one_smul, Scheme.Modules.Hom.id_app]
  rfl

private lemma smulHom_zero (M : X.Modules) : smulHom (0 : Γ(X, ⊤)) M = 0 := by
  ext W x
  simp only [smulHom_app, map_zero, zero_smul, Scheme.Modules.Hom.zero_app]
  rfl

variable {ι : Type*} {c : ComplexShape ι}

/-- Multiplication by a global function, as an endomorphism of a complex of `𝒪_X`-modules. -/
private noncomputable def smulComplex (s : Γ(X, ⊤)) (K : HomologicalComplex X.Modules c) :
    K ⟶ K where
  f i := smulHom s (K.X i)
  comm' i j _ := smulHom_naturality s (K.d i j)

private lemma smulComplex_f (s : Γ(X, ⊤)) (K : HomologicalComplex X.Modules c) (i : ι) :
    (smulComplex s K).f i = smulHom s (K.X i) := rfl

@[reassoc]
private lemma smulComplex_naturality (s : Γ(X, ⊤)) {K L : HomologicalComplex X.Modules c}
    (g : K ⟶ L) :
    smulComplex s K ≫ g = g ≫ smulComplex s L := by
  ext i : 1
  exact smulHom_naturality s (g.f i)

private lemma smulComplex_mul (s t : Γ(X, ⊤)) (K : HomologicalComplex X.Modules c) :
    smulComplex (s * t) K = smulComplex t K ≫ smulComplex s K := by
  ext i : 1
  exact smulHom_mul s t _

private lemma smulComplex_add (s t : Γ(X, ⊤)) (K : HomologicalComplex X.Modules c) :
    smulComplex (s + t) K = smulComplex s K + smulComplex t K := by
  ext i : 1
  exact smulHom_add s t _

private lemma smulComplex_one (K : HomologicalComplex X.Modules c) :
    smulComplex (1 : Γ(X, ⊤)) K = 𝟙 K := by
  ext i : 1
  exact smulHom_one _

private lemma smulComplex_zero (K : HomologicalComplex X.Modules c) :
    smulComplex (0 : Γ(X, ⊤)) K = 0 := by
  ext i : 1
  exact smulHom_zero _

end Smul

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

private lemma stupidGEMap_comp_ι (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGEMap Y i ≫ stupidGEι Y i = stupidGEι Y (i + 1) := by
  ext m
  by_cases h : i + 1 ≤ m
  · simp only [HomologicalComplex.comp_f, stupidGEMap, stupidGEι, dif_pos h,
      dif_pos (by omega : i ≤ m)]
    simp
  · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

/-- The projection `σ^{≥ i} Y ⟶ Y^i[-i]`. -/
private noncomputable def stupidGEπ (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGE Y i ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) i).obj (Y.X i) :=
  HomologicalComplex.mkHomToSingle (eqToHom (stupidGE_X_of_le Y le_rfl)) fun j hj => by
    exact (isZero_stupidGE_X_of_lt Y (by simp at hj; omega)).eq_of_src _ _

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

/-- A complex `L` vanishing below `i` with a map to `Y` that is an isomorphism from degree `i` on
is identified with `σ^{≥ i} Y`. -/
private lemma exists_isIso_comp_stupidGEι {Y L : CochainComplex C ℤ} (i : ℤ) (φ : L ⟶ Y)
    (hL : ∀ m, m < i → IsZero (L.X m)) (hφ : ∀ m, i ≤ m → IsIso (φ.f m)) :
    ∃ ψ : L ⟶ stupidGE Y i, IsIso ψ ∧ ψ ≫ stupidGEι Y i = φ := by
  let ψ : L ⟶ stupidGE Y i :=
    { f := fun m => if h : i ≤ m then φ.f m ≫ eqToHom (stupidGE_X_of_le Y h).symm else 0
      comm' := fun m m' hmm' => by
        obtain rfl : m + 1 = m' := hmm'
        by_cases h : i ≤ m
        · rw [dif_pos h, dif_pos (by omega : i ≤ m + 1), stupidGE_d Y h (by omega)]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [← HomologicalComplex.Hom.comm_assoc]
        · exact (hL m (by omega)).eq_of_src _ _ }
  haveI : ∀ m, IsIso (ψ.f m) := fun m => by
    by_cases h : i ≤ m
    · change IsIso (if h : i ≤ m then φ.f m ≫ eqToHom (stupidGE_X_of_le Y h).symm else 0)
      rw [dif_pos h]
      haveI := hφ m h
      infer_instance
    · exact isIso_of_source_target_iso_zero _ (hL m (by omega)).isoZero
        (isZero_stupidGE_X_of_lt Y (by omega)).isoZero
  refine ⟨ψ, HomologicalComplex.Hom.isIso_of_components _, ?_⟩
  · refine HomologicalComplex.hom_ext _ _ fun m => ?_
    by_cases h : i ≤ m
    · change (if h : i ≤ m then φ.f m ≫ eqToHom (stupidGE_X_of_le Y h).symm else 0) ≫
        (stupidGEι Y i).f m = φ.f m
      rw [dif_pos h, stupidGEι_f_of_le Y h]
      simp
    · exact (hL m (by omega)).eq_of_src _ _

private lemma isZero_stupidGE (Y : CochainComplex C ℤ) (i : ℤ) (hY : ∀ m, i ≤ m → IsZero (Y.X m)) :
    IsZero (stupidGE Y i) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  by_cases h : i ≤ m
  · exact ((hY m h).of_iso (eqToIso (stupidGE_X_of_le Y h))).eq_of_src _ _
  · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

private lemma isZero_stupidGE_X (Y : CochainComplex C ℤ) (i m : ℤ) (hY : IsZero (Y.X m)) :
    IsZero ((stupidGE Y i).X m) := by
  by_cases h : i ≤ m
  · exact hY.of_iso (eqToIso (stupidGE_X_of_le Y h))
  · exact isZero_stupidGE_X_of_lt Y (by omega)

end TruncAbelian

section Biproduct

variable {C : Type*} [Category C] [Abelian C] {J : Type} [Fintype J] [DecidableEq J]

private theorem hasFiniteBiproducts_cochainComplex (C : Type*) [Category C] [Abelian C] :
    HasFiniteBiproducts (CochainComplex C ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] hasFiniteBiproducts_cochainComplex

/-- On homology in a degree where only the summand `j₀` contributes, the map out of a biproduct
of complexes is the map out of that summand. -/
private lemma isIso_homologyMap_biproduct_desc (F : J → CochainComplex C ℤ) {Z : CochainComplex C ℤ}
    (θ : ∀ j, F j ⟶ Z) (m : ℤ) (j₀ : J) (hF : ∀ j, j ≠ j₀ → IsZero ((F j).homology m))
    (hθ : IsIso (HomologicalComplex.homologyMap (θ j₀) m)) :
    IsIso (HomologicalComplex.homologyMap (biproduct.desc θ) m) := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) m
  have hF' : ∀ j, j ≠ j₀ → IsZero (H.obj (F j)) := hF
  have h0 : ∀ j, j ≠ j₀ → H.map (biproduct.π F j ≫ biproduct.ι F j) = 0 := fun j hj => by
    rw [H.map_comp, (hF' j hj).eq_of_tgt (H.map (biproduct.π F j)) 0, zero_comp]
  have hdesc : H.map (biproduct.desc θ) = H.map (biproduct.π F j₀) ≫ H.map (θ j₀) := by
    rw [biproduct.desc_eq, H.map_sum, Finset.sum_eq_single j₀]
    · exact H.map_comp _ _
    · intro j _ hj
      rw [H.map_comp, (hF' j hj).eq_of_src (H.map (θ j)) 0, comp_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  have hπ : IsIso (H.map (biproduct.π F j₀)) := by
    refine ⟨H.map (biproduct.ι F j₀), ?_, ?_⟩
    · have htot := congrArg H.map (biproduct.total (f := F))
      rw [H.map_id, H.map_sum, Finset.sum_eq_single j₀ (fun j _ hj => h0 j hj)
        (fun h => absurd (Finset.mem_univ j₀) h)] at htot
      rw [← H.map_comp]
      exact htot
    · rw [← H.map_comp, biproduct.ι_π_self, H.map_id]
  change IsIso (H.map (biproduct.desc θ))
  rw [hdesc]
  exact IsIso.comp_isIso' hπ hθ

private lemma isIso_homologyMap_biproduct_desc_of_isZero (F : J → CochainComplex C ℤ)
    {Z : CochainComplex C ℤ} (θ : ∀ j, F j ⟶ Z) (m : ℤ) (hF : ∀ j, IsZero ((F j).homology m))
    (hZ : IsZero (Z.homology m)) :
    IsIso (HomologicalComplex.homologyMap (biproduct.desc θ) m) := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) m
  have hF' : ∀ j, IsZero (H.obj (F j)) := hF
  have hB : IsZero (H.obj (⨁ F)) := by
    rw [IsZero.iff_id_eq_zero]
    have htot := congrArg H.map (biproduct.total (f := F))
    rw [H.map_id, H.map_sum] at htot
    rw [← htot]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [H.map_comp, (hF' j).eq_of_tgt (H.map (biproduct.π F j)) 0, zero_comp]
  exact isIso_of_source_target_iso_zero _ hB.isoZero hZ.isoZero

private lemma isZero_biproduct_X (F : J → CochainComplex C ℤ) (p : ℤ)
    (hF : ∀ j, IsZero ((F j).X p)) : IsZero ((⨁ F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) p
  have hF' : ∀ j, IsZero (E.obj (F j)) := hF
  have htot := congrArg E.map (biproduct.total (f := F))
  rw [E.map_id, E.map_sum] at htot
  change 𝟙 (E.obj (⨁ F)) = 0
  rw [← htot]
  exact Finset.sum_eq_zero fun j _ => by
    rw [E.map_comp, (hF' j).eq_of_tgt (E.map (biproduct.π F j)) 0, zero_comp]

end Biproduct

section CentralSmul

variable {R : Type*} [Ring R] (s : R) (hs : ∀ r : R, s * r = r * s)

/-- Multiplication by a central element, as an endomorphism of a module. -/
private noncomputable def smulCentral (N : ModuleCat R) : N ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun x => s • x
      map_add' := smul_add s
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [smul_smul, hs, mul_smul] }

@[reassoc]
private lemma smulCentral_naturality {N N' : ModuleCat R} (g : N ⟶ N') :
    g ≫ smulCentral s hs N' = smulCentral s hs N ≫ g := by
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  exact ((g.hom.map_smul s x)).symm

/-- On homology, a chain map which is multiplication by a central element in every degree is
multiplication by that element. -/
private lemma homologyMap_eq_smulCentral {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (μ : K ⟶ K)
    (hμ : ∀ i, μ.f i = smulCentral s hs (K.X i)) (i : ι) :
    HomologicalComplex.homologyMap μ i = smulCentral s hs (K.homology i) := by
  have hc : HomologicalComplex.cyclesMap μ i = smulCentral s hs (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, hμ, smulCentral_naturality]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc,
    smulCentral_naturality]

end CentralSmul

section KModule

open MMP.Analytic

attribute [local instance] additive_globalSections additive_godementResolution

variable {X : Scheme.{u}}

private theorem additive_godementSections (T : TopCat.{u}) : (godementSections T).Additive := by
  dsimp only [godementSections]
  infer_instance

attribute [local instance] additive_godementSections

private theorem additive_hypercohomology (T : TopCat.{u}) (m : ℤ) :
    (hypercohomology T m).Additive := by
  dsimp only [hypercohomology]
  infer_instance

attribute [local instance] additive_hypercohomology

/-- The underlying complex of abelian sheaves of a complex of `𝒪_X`-modules. -/
private noncomputable abbrev toSheafX (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  SheafOfModules.toSheaf X.ringCatSheaf

private theorem additive_toSheafX (X : Scheme.{u}) : (toSheafX X).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

attribute [local instance] additive_toSheafX

private noncomputable abbrev toSheafComplex (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) ℤ :=
  (toSheafX X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total complex of Godement sections of the underlying complex of abelian sheaves. -/
private noncomputable abbrev totComplex (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  toSheafComplex X ⋙ (godementSections X.toTopCat).mapHomologicalComplex _ ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ)

/-- Hypercohomology of the underlying complex of abelian sheaves. -/
private noncomputable abbrev hyp (X : Scheme.{u}) (m : ℤ) :
    CochainComplex X.Modules ℤ ⥤ AddCommGrpCat.{u} :=
  totComplex X ⋙ HomologicalComplex.homologyFunctor _ _ m

private theorem additive_toSheafComplex : (toSheafComplex X).Additive :=
  Functor.map_homogical_complex_additive _ _

attribute [local instance] additive_toSheafComplex

private theorem additive_hyp (m : ℤ) : (hyp X m).Additive := by
  dsimp only [hyp, totComplex]
  infer_instance

attribute [local instance] additive_hyp

variable {k : Type u} [Field k] (φ : k →+* Γ(X, ⊤))

/-- The field `k`, acting on hypercohomology through `φ : k → Γ(X, 𝒪_X)`. -/
@[nolint unusedArguments]
private def KAct (_φ : k →+* Γ(X, ⊤)) : Type u := k

private noncomputable abbrev KAct.field : Field (KAct φ) := inferInstanceAs (Field k)

attribute [local instance] KAct.field

/-- The global function by which an element of `KAct φ` acts. -/
private def KAct.toΓ : KAct φ →+* Γ(X, ⊤) := φ

/-- The action of `k` on hypercohomology, through the action of `Γ(X, 𝒪_X)` on the complex. -/
private noncomputable def hypScalar (m : ℤ) (K : CochainComplex X.Modules ℤ) :
    KAct φ →+* AddMonoid.End ((hyp X m).obj K) where
  toFun c := ((hyp X m).map (smulComplex (KAct.toΓ φ c) K)).hom
  map_one' := by
    ext x
    change ((hyp X m).map (smulComplex (KAct.toΓ φ 1) K)) x = x
    rw [map_one, smulComplex_one, CategoryTheory.Functor.map_id]
    rfl
  map_mul' c d := by
    ext x
    change ((hyp X m).map (smulComplex (KAct.toΓ φ (c * d)) K)) x =
      ((hyp X m).map (smulComplex (KAct.toΓ φ c) K))
        (((hyp X m).map (smulComplex (KAct.toΓ φ d) K)) x)
    rw [map_mul, smulComplex_mul, Functor.map_comp]
    rfl
  map_zero' := by
    ext x
    change ((hyp X m).map (smulComplex (KAct.toΓ φ 0) K)) x = 0
    rw [map_zero, smulComplex_zero, Functor.map_zero]
    rfl
  map_add' c d := by
    ext x
    change ((hyp X m).map (smulComplex (KAct.toΓ φ (c + d)) K)) x =
      ((hyp X m).map (smulComplex (KAct.toΓ φ c) K)) x +
        ((hyp X m).map (smulComplex (KAct.toΓ φ d) K)) x
    rw [map_add, smulComplex_add, Functor.map_add]
    rfl

/-- The `k`-module structure on hypercohomology. -/
private noncomputable abbrev hypModule (m : ℤ) (K : CochainComplex X.Modules ℤ) :
    Module (KAct φ) ((hyp X m).obj K) :=
  Module.compHom _ (hypScalar φ m K)

attribute [local instance] hypModule

private lemma hyp_smul_def (m : ℤ) (K : CochainComplex X.Modules ℤ) (c : KAct φ)
    (x : (hyp X m).obj K) : c • x = (hyp X m).map (smulComplex (KAct.toΓ φ c) K) x := rfl

/-- Hypercohomology of a morphism of complexes is `k`-linear. -/
private noncomputable def hypMap (m : ℤ) {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L) :
    (hyp X m).obj K →ₗ[KAct φ] (hyp X m).obj L where
  toFun := (hyp X m).map g
  map_add' := map_add _
  map_smul' := fun c x => by
    simp only [hyp_smul_def, RingHom.id_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      smulComplex_naturality]

private lemma hypMap_comp (m : ℤ) {K L M : CochainComplex X.Modules ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    hypMap φ m (g ≫ h) = (hypMap φ m h).comp (hypMap φ m g) := by
  ext x
  change (hyp X m).map (g ≫ h) x = (hyp X m).map h ((hyp X m).map g x)
  rw [Functor.map_comp]
  rfl

private lemma hypMap_id (m : ℤ) (K : CochainComplex X.Modules ℤ) :
    hypMap φ m (𝟙 K) = LinearMap.id := by
  ext x
  change (hyp X m).map (𝟙 K) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Exactness, read as the equality of a kernel and a range. -/
private lemma ker_eq_range_of {R A B C : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (F : A →ₗ[R] B) (G : B →ₗ[R] C)
    (h₁ : ∀ x, G (F x) = 0) (h₂ : ∀ y, G y = 0 → ∃ x, F x = y) :
    LinearMap.ker G = LinearMap.range F := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  exact ⟨h₂ y, fun ⟨x, hx⟩ => hx ▸ h₁ x⟩

/-- **The long exact hypercohomology sequence** of a degreewise short exact sequence of bounded
complexes of `𝒪_X`-modules, with `k`-linear maps. -/
private theorem exists_hyp_longExact (S : ShortComplex (CochainComplex X.Modules ℤ))
    (hS : ∀ i, (S.map (HomologicalComplex.eval _ _ i)).ShortExact) (a b : ℤ)
    (h₁ : ∀ i, (i < a ∨ b < i) → IsZero (S.X₁.X i)) (h₂ : ∀ i, (i < a ∨ b < i) → IsZero (S.X₂.X i))
    (h₃ : ∀ i, (i < a ∨ b < i) → IsZero (S.X₃.X i)) :
    ∃ δ : ∀ m : ℤ, (hyp X m).obj S.X₃ →ₗ[KAct φ] (hyp X (m + 1)).obj S.X₁,
      (∀ m, LinearMap.ker (hypMap φ (m + 1) S.f) = LinearMap.range (δ m)) ∧
      (∀ m, LinearMap.ker (hypMap φ m S.g) = LinearMap.range (hypMap φ m S.f)) ∧
      (∀ m, LinearMap.ker (δ m) = LinearMap.range (hypMap φ m S.g)) := by
  let T : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
    SheafOfModules.toSheaf X.ringCatSheaf
  haveI : T.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  haveI : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
  haveI : PreservesFiniteColimits T :=
    ModuleSheafCohomology.toSheaf_preservesFiniteColimits _ X.ringCatSheaf
  set S' := S.map (toSheafComplex X) with hS'def
  have hS' : ∀ i, (S'.map (HomologicalComplex.eval _ _ i)).ShortExact := fun i => by
    exact (hS i).map_of_exact T
  have hz : ∀ (K : CochainComplex X.Modules ℤ) (i : ℤ), IsZero (K.X i) →
      IsZero (((toSheafComplex X).obj K).X i) := fun K i h =>
    (SheafOfModules.toSheaf X.ringCatSheaf).map_isZero h
  have hb : ∃ a b, S'.X₁.IsStrictlyGE a ∧ S'.X₁.IsStrictlyLE b ∧ S'.X₂.IsStrictlyGE a ∧
      S'.X₂.IsStrictlyLE b ∧ S'.X₃.IsStrictlyGE a ∧ S'.X₃.IsStrictlyLE b :=
    ⟨a, b, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => hz _ _ (h₁ i (Or.inl hi)),
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => hz _ _ (h₁ i (Or.inr hi)),
      (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => hz _ _ (h₂ i (Or.inl hi)),
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => hz _ _ (h₂ i (Or.inr hi)),
      (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => hz _ _ (h₃ i (Or.inl hi)),
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => hz _ _ (h₃ i (Or.inr hi))⟩
  obtain ⟨hT, -⟩ :=
    (MMP.Analytic.sheafCohomology_toolkit.{u, 0, 0, 0, 0} X.toTopCat).2.2.1.2.1 S' hS' hb
  let G := totComplex X
  have hG : (S.map G).ShortExact := hT
  let σ : KAct φ → (S ⟶ S) := fun c =>
    { τ₁ := smulComplex (KAct.toΓ φ c) S.X₁
      τ₂ := smulComplex (KAct.toΓ φ c) S.X₂
      τ₃ := smulComplex (KAct.toΓ φ c) S.X₃
      comm₁₂ := smulComplex_naturality _ S.f
      comm₂₃ := smulComplex_naturality _ S.g }
  have hfg : ∀ m : ℤ, HomologicalComplex.homologyMap (S.map G).f m ≫
      HomologicalComplex.homologyMap (S.map G).g m = 0 := fun m => by
    rw [← HomologicalComplex.homologyMap_comp, (S.map G).zero, HomologicalComplex.homologyMap_zero]
  let δ : ∀ m : ℤ, (hyp X m).obj S.X₃ →ₗ[KAct φ] (hyp X (m + 1)).obj S.X₁ := fun m =>
    { toFun := hG.δ m (m + 1) rfl
      map_add' := map_add _
      map_smul' := fun c x => by
        have h := HomologicalComplex.HomologySequence.δ_naturality (G.mapShortComplex.map (σ c))
          hG hG m (m + 1) rfl
        exact (ConcreteCategory.congr_hom h x).symm }
  have hδ : ∀ m (y : (hyp X m).obj S.X₃), δ m y = hG.δ m (m + 1) rfl y := fun _ _ => rfl
  refine ⟨δ, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · refine ker_eq_range_of _ _ (fun x => ?_) fun y hy => ?_
    · rw [hδ]
      exact ConcreteCategory.congr_hom (hG.δ_comp m (m + 1) rfl) x
    · obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 (hG.homology_exact₁ m (m + 1) rfl) y hy
      exact ⟨x, (hδ m x).trans hx⟩
  · exact ker_eq_range_of _ _ (fun x => ConcreteCategory.congr_hom (hfg m) x)
      fun y hy => (ShortComplex.ab_exact_iff _).1 (hG.homology_exact₂ m) y hy
  · refine ker_eq_range_of _ _ (fun x => ?_) fun y hy => ?_
    · rw [hδ]
      exact ConcreteCategory.congr_hom (hG.comp_δ m (m + 1) rfl) x
    · rw [hδ] at hy
      exact (ShortComplex.ab_exact_iff _).1 (hG.homology_exact₃ m (m + 1) rfl) y hy

open Module in
/-- For an exact sequence `E' → B → A → E → B'` with `B`, `A`, `E` finite-dimensional,
`dim A + rk(E' → B) + rk(E → B') = dim B + dim E`. -/
public theorem finrank_add_finrank_range_add_finrank_range {k : Type*} [Field k]
    {B A E E' B' : Type*} [AddCommGroup B] [Module k B] [AddCommGroup A]
    [Module k A] [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']
    [AddCommGroup B'] [Module k B'] [FiniteDimensional k B] [FiniteDimensional k A]
    [FiniteDimensional k E] (δ' : E' →ₗ[k] B) (ι : B →ₗ[k] A) (π : A →ₗ[k] E) (δ : E →ₗ[k] B')
    (h₁ : LinearMap.ker ι = LinearMap.range δ') (h₂ : LinearMap.ker π = LinearMap.range ι)
    (h₃ : LinearMap.ker δ = LinearMap.range π) :
    finrank k A + finrank k (LinearMap.range δ') + finrank k (LinearMap.range δ) =
      finrank k B + finrank k E := by
  have a := LinearMap.finrank_range_add_finrank_ker ι
  have b := LinearMap.finrank_range_add_finrank_ker π
  have c := LinearMap.finrank_range_add_finrank_ker δ
  rw [h₁] at a
  rw [h₂] at b
  rw [h₃] at c
  omega

open Module in
/-- **Degeneration from dimensions.** Let `A_i^m` (`i ≤ N + 1`, `A_{N+1} = 0`) and `E_i^m` be
finite-dimensional, with long exact sequences `A_{i+1}^m → A_i^m → E_i^m → A_{i+1}^{m+1}`. If
`dim A_0^m = ∑_{i ≤ N} dim E_i^m` for every `m`, then every `A_{i+1}^m → A_i^m` is injective. -/
private theorem injective_of_finrank_eq_sum {k : Type*} [Field k] (N : ℕ) (A E : ℕ → ℤ → Type*)
    [∀ i m, AddCommGroup (A i m)] [∀ i m, Module k (A i m)] [∀ i m, FiniteDimensional k (A i m)]
    [∀ i m, AddCommGroup (E i m)] [∀ i m, Module k (E i m)] [∀ i m, FiniteDimensional k (E i m)]
    (ι : ∀ i m, A (i + 1) m →ₗ[k] A i m) (π : ∀ i m, A i m →ₗ[k] E i m)
    (δ : ∀ i m, E i m →ₗ[k] A (i + 1) (m + 1))
    (h₁ : ∀ i m, LinearMap.ker (ι i (m + 1)) = LinearMap.range (δ i m))
    (h₂ : ∀ i m, LinearMap.ker (π i m) = LinearMap.range (ι i m))
    (h₃ : ∀ i m, LinearMap.ker (δ i m) = LinearMap.range (π i m))
    (hN : ∀ m, Subsingleton (A (N + 1) m))
    (hdim : ∀ m, finrank k (A 0 m) = ∑ i ∈ Finset.range (N + 1), finrank k (E i m)) :
    ∀ i ≤ N, ∀ m, Function.Injective (ι i m) := by
  set r : ℕ → ℤ → ℕ := fun i m ↦ finrank k (LinearMap.range (δ i m)) with hr
  have step : ∀ i m, finrank k (A i (m + 1)) + r i m + r i (m + 1) =
      finrank k (A (i + 1) (m + 1)) + finrank k (E i (m + 1)) := fun i m ↦
    finrank_add_finrank_range_add_finrank_range (δ i m) (ι i (m + 1)) (π i (m + 1))
      (δ i (m + 1)) (h₁ i m) (h₂ i (m + 1)) (h₃ i (m + 1))
  have hsum : ∀ m, finrank k (A 0 (m + 1)) + ∑ i ∈ Finset.range (N + 1), (r i m + r i (m + 1)) =
      ∑ i ∈ Finset.range (N + 1), finrank k (E i (m + 1)) := by
    intro m
    have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (N + 1)) ↦ step i m)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    rw [Finset.sum_range_succ' (fun i ↦ finrank k (A i (m + 1))),
      Finset.sum_range_succ (fun i ↦ finrank k (A (i + 1) (m + 1))),
      Module.finrank_zero_of_subsingleton (M := A (N + 1) (m + 1))] at h
    rw [Finset.sum_add_distrib]
    omega
  have hr0 : ∀ i ≤ N, ∀ m, r i m = 0 := by
    intro i hi m
    have h := hsum m
    rw [← hdim (m + 1)] at h
    have : r i m + r i (m + 1) ≤ ∑ i ∈ Finset.range (N + 1), (r i m + r i (m + 1)) :=
      Finset.single_le_sum (f := fun i ↦ r i m + r i (m + 1)) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    omega
  intro i hi m
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by ring⟩
  rw [← LinearMap.ker_eq_bot, h₁, ← Submodule.finrank_eq_zero]
  exact hr0 i hi m

/-- The middle term of an exact sequence of finite-dimensional spaces is finite-dimensional. -/
private theorem finiteDimensional_of_exact {K A B E : Type*} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup E] [Module K E] [FiniteDimensional K B]
    [FiniteDimensional K E] (ι : B →ₗ[K] A) (π : A →ₗ[K] E)
    (h : LinearMap.ker π = LinearMap.range ι) : FiniteDimensional K A := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker π ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, h, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map ι

private lemma subsingleton_hyp_of_isZero (m : ℤ) {K : CochainComplex X.Modules ℤ} (hK : IsZero K) :
    Subsingleton ((hyp X m).obj K) :=
  AddCommGrpCat.isZero_iff_subsingleton.mp ((hyp X m).map_isZero hK)

private lemma bijective_hyp_map_of_isIso (m : ℤ) {K L : CochainComplex X.Modules ℤ} (g : K ⟶ L)
    [IsIso g] : Function.Bijective ((hyp X m).map g) :=
  ConcreteCategory.bijective_of_isIso ((hyp X m).map g)

private lemma hypMap_add (m : ℤ) {K L : CochainComplex X.Modules ℤ} (g h : K ⟶ L) :
    hypMap φ m (g + h) = hypMap φ m g + hypMap φ m h := by
  ext x
  change (hyp X m).map (g + h) x = (hyp X m).map g x + (hyp X m).map h x
  rw [Functor.map_add]
  rfl

private lemma hypMap_zero (m : ℤ) {K L : CochainComplex X.Modules ℤ} :
    hypMap φ m (0 : K ⟶ L) = 0 := by
  ext x
  change (hyp X m).map 0 x = 0
  rw [Functor.map_zero]
  rfl

private lemma hypMap_sum (m : ℤ) {K L : CochainComplex X.Modules ℤ} {J : Type*} (s : Finset J)
    (g : J → (K ⟶ L)) : hypMap φ m (∑ j ∈ s, g j) = ∑ j ∈ s, hypMap φ m (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hypMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hypMap_add, ih]

attribute [local instance] hasFiniteBiproducts_cochainComplex

/-- Hypercohomology commutes with finite biproducts of complexes. -/
private theorem bijective_hypMap_pi {J : Type} [Fintype J] [DecidableEq J]
    (F : J → CochainComplex X.Modules ℤ) (m : ℤ) :
    Function.Bijective (LinearMap.pi fun j => hypMap φ m (biproduct.π F j)) := by
  have htot : ∀ x : (hyp X m).obj (⨁ F), ∑ j, hypMap φ m (biproduct.ι F j)
      (hypMap φ m (biproduct.π F j) x) = x := fun x => by
    have h := congrArg (fun g => hypMap φ m g x) (biproduct.total (f := F))
    simpa only [hypMap_sum, LinearMap.sum_apply, hypMap_comp,
      LinearMap.comp_apply, hypMap_id, LinearMap.id_apply] using h
  refine ⟨fun x y hxy => ?_, fun y => ⟨∑ j, hypMap φ m (biproduct.ι F j) (y j), ?_⟩⟩
  · rw [← htot x, ← htot y]
    exact Finset.sum_congr rfl fun j _ => congrArg _ (congrFun hxy j)
  · funext j'
    simp only [LinearMap.pi_apply, map_sum, ← LinearMap.comp_apply, ← hypMap_comp]
    rw [Finset.sum_eq_single j']
    · rw [biproduct.ι_π_self, hypMap_id, LinearMap.id_apply]
    · intro j _ hj
      rw [biproduct.ι_π_ne _ hj, hypMap_zero, LinearMap.zero_apply]
    · exact fun h => absurd (Finset.mem_univ j') h

/-- A quasi-isomorphism of complexes of `𝒪_X`-modules concentrated in nonnegative degrees induces
an isomorphism on hypercohomology. -/
private theorem bijective_hyp_map_of_quasiIso (m : ℤ) {K L : CochainComplex X.Modules ℤ}
    (g : K ⟶ L) [QuasiIso g] (hK : ∀ p < 0, IsZero (K.X p)) (hL : ∀ p < 0, IsZero (L.X p)) :
    Function.Bijective ((hyp X m).map g) := by
  let T : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
    SheafOfModules.toSheaf X.ringCatSheaf
  haveI : T.Additive := ⟨fun {_ _ _ _} => rfl⟩
  haveI : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
  haveI : PreservesFiniteColimits T :=
    ModuleSheafCohomology.toSheaf_preservesFiniteColimits _ X.ringCatSheaf
  haveI : QuasiIso ((toSheafComplex X).map g) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology g T
  haveI : IsIso ((hyp X m).map g) := isIso_hypercohomology_map X.toTopCat
    ((toSheafComplex X).map g) (fun p hp => T.map_isZero (hK p hp))
    (fun p hp => T.map_isZero (hL p hp)) m
  exact ConcreteCategory.bijective_of_isIso _

private lemma smulComplex_single (s : Γ(X, ⊤)) (q : ℤ) (N : X.Modules) :
    smulComplex s ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj N) =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) q).map (smulHom s N) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h : i = q
  · subst h
    rw [HomologicalComplex.single_map_f_self, smulComplex_f, ← smulHom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_src _ _

open Stacks.Frobenius in
/-- On the underlying abelian sheaf, `F_*M` is `M`, with `s` acting by `s ^ p`. -/
private lemma toSheaf_map_smulHom_pushforward_frobenius {p : ℕ} [Fact p.Prime]
    (hX : IsInCharacteristic X p) (s : Γ(X, ⊤)) (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        (smulHom s ((Scheme.Modules.pushforward (absoluteFrobenius X p hX)).obj M)) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map (smulHom (s ^ p) M) := by
  refine MMP.Analytic.sheafHom_ext fun U x => ?_
  change (smulHom s ((Scheme.Modules.pushforward (absoluteFrobenius X p hX)).obj M)).app U.unop x =
    (smulHom (s ^ p) M).app U.unop x
  change (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s •
      (show Γ((Scheme.Modules.pushforward (absoluteFrobenius X p hX)).obj M, U.unop) from x)) =
    X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (s ^ p) • (show Γ(M, U.unop) from x)
  rw [map_pow]
  change (show Γ(X, U.unop) from (absoluteFrobenius X p hX).app U.unop
    (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)) • (show Γ(M, U.unop) from x) = _
  rw [absoluteFrobenius_app_apply]

open Stacks.Frobenius in
/-- **Hypercohomology of a Frobenius pushforward.** `ℍ^m(F_*M[-q])` is `ℍ^m(M[-q])` as an
abelian group, with `c ∈ k` acting by `c ^ p`. -/
private theorem exists_addEquiv_hyp_single_pushforward_frobenius {p : ℕ} [Fact p.Prime]
    (hX : IsInCharacteristic X p) (M : X.Modules) (q m : ℤ) :
    ∃ e : (hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
        ((Scheme.Modules.pushforward (absoluteFrobenius X p hX)).obj M)) ≃+
        (hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M),
      ∀ (c : KAct φ) x, e (c • x) = (c ^ p) • e x := by
  let T : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
    SheafOfModules.toSheaf X.ringCatSheaf
  haveI : T.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let σ := HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) q
  let N := (Scheme.Modules.pushforward (absoluteFrobenius X p hX)).obj M
  let ε : (toSheafComplex X).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj N) ≅
      (toSheafComplex X).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) :=
    σ.app N ≪≫ (σ.app M).symm
  have hε : ∀ c : KAct φ, (toSheafComplex X).map (smulComplex (KAct.toΓ φ c)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj N)) ≫ ε.hom =
      ε.hom ≫ (toSheafComplex X).map (smulComplex (KAct.toΓ φ (c ^ p))
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M)) := fun c => by
    have h₁ := σ.hom.naturality (smulHom (KAct.toΓ φ c) N)
    have h₂ := σ.inv.naturality (smulHom (KAct.toΓ φ (c ^ p)) M)
    have h₃ : T.map (smulHom (KAct.toΓ φ c) N) = T.map (smulHom (KAct.toΓ φ (c ^ p)) M) := by
      rw [map_pow]
      exact toSheaf_map_smulHom_pushforward_frobenius hX _ M
    simp only [Functor.comp_map] at h₁ h₂
    have key : (T.mapHomologicalComplex _).map ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        q).map (smulHom (KAct.toΓ φ c) N)) ≫ σ.hom.app N ≫ σ.inv.app M =
        σ.hom.app N ≫ σ.inv.app M ≫ (T.mapHomologicalComplex _).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).map
            (smulHom (KAct.toΓ φ (c ^ p)) M)) :=
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ σ.inv.app M) h₁)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => σ.hom.app N ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) q).map g ≫ σ.inv.app M) h₃).trans
            (congrArg (σ.hom.app N ≫ ·) h₂)))
    rw [smulComplex_single, smulComplex_single]
    exact key.trans (Category.assoc _ _ _).symm
  refine ⟨((hypercohomology X.toTopCat m).mapIso ε).addCommGroupIsoToAddEquiv, fun c x => ?_⟩
  have h := congrArg (fun g => (hypercohomology X.toTopCat m).map g x) (hε c)
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h
  exact h

open Module in
/-- An additive bijection which is semilinear along a bijection of scalars preserves dimension. -/
private lemma finrank_eq_and_finiteDimensional_of_semilinear {K : Type*} {A B : Type u} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] (σ : K → K)
    (hσ : Function.Bijective σ) (e : A ≃+ B) (he : ∀ c x, e (c • x) = σ c • e x) :
    finrank K A = finrank K B ∧ (FiniteDimensional K B → FiniteDimensional K A) := by
  have hr := rank_eq_of_equiv_equiv σ e hσ he
  refine ⟨by simp only [Module.finrank, hr], fun h => ?_⟩
  change Module.Finite K A
  rw [← Module.rank_lt_aleph0_iff, hr]
  exact Module.rank_lt_aleph0 K B

private lemma bijective_pow_kAct {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectField k] :
    Function.Bijective (fun c : KAct φ => c ^ p) := by
  have : PerfectRing k p := PerfectField.toPerfectRing p
  exact bijective_frobenius k p

open Module in
/-- **Degeneration from dimensions, for hypercohomology.** Let `Y` be a complex of `𝒪_X`-modules
concentrated in degrees `[0, N]` such that every `ℍ^m(Y^i[-i])` is finite-dimensional over `k`
and `dim ℍ^m(Y) = ∑_{i ≤ N} dim ℍ^m(Y^i[-i])`. Then for every complex `L` vanishing below `i`
with a map `L ⟶ Y` which is an isomorphism from degree `i` on, `ℍ^m(L) ⟶ ℍ^m(Y)` is injective. -/
private theorem injective_hyp_map_of_finrank_eq_sum (Y : CochainComplex X.Modules ℤ) (N : ℕ)
    (hY : ∀ m, (m < 0 ∨ (N : ℤ) < m) → IsZero (Y.X m))
    (hfin : ∀ (i : ℕ) (m : ℤ), FiniteDimensional (KAct φ)
      ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (i : ℤ)).obj (Y.X i))))
    (hdim : ∀ m, finrank (KAct φ) ((hyp X m).obj Y) = ∑ i ∈ Finset.range (N + 1),
      finrank (KAct φ)
        ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (i : ℤ)).obj (Y.X i))))
    (i : ℕ) (L : CochainComplex X.Modules ℤ) (ψ : L ⟶ Y) (hL : ∀ m : ℤ, m < i → IsZero (L.X m))
    (hψ : ∀ m : ℤ, (i : ℤ) ≤ m → IsIso (ψ.f m)) (m : ℤ) :
    Function.Injective ((hyp X m).map ψ) := by
  let A : ℕ → ℤ → Type u := fun i m => (hyp X m).obj (stupidGE Y i)
  let E : ℕ → ℤ → Type u := fun i m =>
    (hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (i : ℤ)).obj (Y.X i))
  have hS : ∀ i : ℕ, ∃ δ : ∀ m : ℤ, E i m →ₗ[KAct φ] A (i + 1) (m + 1),
      (∀ m, LinearMap.ker (hypMap φ (m + 1) (stupidGEMap Y i)) = LinearMap.range (δ m)) ∧
      (∀ m, LinearMap.ker (hypMap φ m (stupidGEπ Y i)) =
        LinearMap.range (hypMap φ m (stupidGEMap Y i))) ∧
      (∀ m, LinearMap.ker (δ m) = LinearMap.range (hypMap φ m (stupidGEπ Y i))) := fun i =>
    exists_hyp_longExact φ (stupidGEShortComplex Y i) (stupidGEShortComplex_shortExact Y i) 0 N
      (fun m hm => isZero_stupidGE_X Y _ m (hY m hm))
      (fun m hm => isZero_stupidGE_X Y _ m (hY m hm))
      (fun m hm => by
        by_cases h : m = i
        · subst h
          exact (hY _ hm).of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) _ _)
        · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) _ _ m h)
  choose δ hδ₁ hδ₂ hδ₃ using hS
  have hzero : ∀ j : ℕ, N + 1 ≤ j → IsZero (stupidGE Y j) := fun j hj =>
    isZero_stupidGE Y _ fun m hm => hY m (Or.inr (by omega))
  have hfinA : ∀ j m, FiniteDimensional (KAct φ) (A j m) := by
    have key : ∀ d : ℕ, ∀ j : ℕ, N + 1 ≤ j + d → ∀ m, FiniteDimensional (KAct φ) (A j m) := by
      intro d
      induction d with
      | zero =>
        intro j hj m
        haveI := subsingleton_hyp_of_isZero m (hzero j (by omega))
        exact Module.Finite.of_finite
      | succ d ih =>
        intro j hj m
        by_cases hjN : N + 1 ≤ j
        · haveI := subsingleton_hyp_of_isZero m (hzero j hjN)
          exact Module.Finite.of_finite
        · haveI : FiniteDimensional (KAct φ) ((hyp X m).obj (stupidGE Y ((j : ℤ) + 1))) :=
            ih (j + 1) (by omega) m
          haveI := hfin j m
          exact finiteDimensional_of_exact (hypMap φ m (stupidGEMap Y j))
            (hypMap φ m (stupidGEπ Y j)) (hδ₂ j m)
    exact fun j m => key (N + 1) j (by omega) m
  have hN : ∀ m, Subsingleton (A (N + 1) m) := fun m =>
    subsingleton_hyp_of_isZero m (hzero _ le_rfl)
  have hdim' : ∀ m, finrank (KAct φ) (A 0 m) =
      ∑ i ∈ Finset.range (N + 1), finrank (KAct φ) (E i m) := by
    intro m
    haveI := isIso_stupidGEι Y ((0 : ℕ) : ℤ) fun m hm => hY m (Or.inl hm)
    rw [← hdim m]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective (hypMap φ m (stupidGEι Y ((0 : ℕ) : ℤ)))
      (bijective_hyp_map_of_isIso m _))
  have hinj := injective_of_finrank_eq_sum N A E (fun i m => hypMap φ m (stupidGEMap Y i))
    (fun i m => hypMap φ m (stupidGEπ Y i)) δ hδ₁ hδ₂ hδ₃ hN hdim'
  have hcomp : ∀ {P Q R : AddCommGrpCat.{u}} (f : P ⟶ Q) (g : Q ⟶ R), Function.Injective f →
      Function.Injective g → Function.Injective (f ≫ g) := fun f g hf hg x y h =>
    hf (hg (by simpa only [ConcreteCategory.comp_apply] using h))
  have hincl : ∀ j : ℕ, ∀ m, Function.Injective ((hyp X m).map (stupidGEι Y j)) := by
    intro j
    induction j with
    | zero =>
      intro m
      haveI := isIso_stupidGEι Y ((0 : ℕ) : ℤ) fun m hm => hY m (Or.inl hm)
      exact (bijective_hyp_map_of_isIso m _).1
    | succ j ih =>
      intro m
      rw [show stupidGEι Y ((j + 1 : ℕ) : ℤ) = stupidGEMap Y j ≫ stupidGEι Y j from
        (stupidGEMap_comp_ι Y j).symm, Functor.map_comp]
      refine hcomp _ _ ?_ (ih m)
      by_cases hj : j ≤ N
      · exact hinj j hj m
      · haveI := subsingleton_hyp_of_isZero m (hzero (j + 1) (by omega))
        exact Function.injective_of_subsingleton _
  obtain ⟨ψ', hiso, hψ'⟩ := exists_isIso_comp_stupidGEι (i : ℤ) ψ hL hψ
  rw [← hψ', Functor.map_comp]
  exact hcomp _ _ (bijective_hyp_map_of_isIso m ψ').1 (hincl i m)

/-- The Frobenius pushforward `F_*K^•` of the logarithmic de Rham complex is concentrated in
degrees `[0, n]`. -/
private lemma isZero_complexZ_X {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectField k] {n : ℕ}
    {f : X ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f] {ι : Type*} [Fintype ι]
    [HasDerivedCategory.{u} X.Modules] (D : FrobeniusSplittingData p k n f ι) (m : ℤ)
    (hm : m < 0 ∨ (n : ℤ) < m) : IsZero (D.complexZ.X m) := by
  rcases hm with hm | hm
  · exact D.complexZ.isZero_of_isStrictlyGE 0 m hm
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j := ⟨m.toNat, by omega⟩
    exact ((Scheme.Modules.pushforward _).map_isZero (D.isZero_K_of_lt (by omega : n < j))).of_iso
      (D.complexZXIso j)

open Module in
/-- **Frobenius twist does not change dimensions.** `ℍ^m(F_*K^q[-q])` is `ℍ^m(K^q[-q])` with
`c ∈ k` acting by `c ^ p`; `k` being perfect, the two have the same dimension. -/
private theorem finrank_hyp_single_complexZ_X {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectField k]
    {n : ℕ} {f : X ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f] {ι : Type*}
    [Fintype ι] [HasDerivedCategory.{u} X.Modules] (D : FrobeniusSplittingData p k n f ι) (q : ℕ)
    (m : ℤ) [FiniteDimensional (KAct φ)
      ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (q : ℤ)).obj (D.K q)))] :
    finrank (KAct φ) ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        (q : ℤ)).obj (D.complexZ.X q))) = finrank (KAct φ)
          ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (q : ℤ)).obj
            (D.K q))) ∧
      FiniteDimensional (KAct φ) ((hyp X m).obj ((HomologicalComplex.single _
        (ComplexShape.up ℤ) (q : ℤ)).obj (D.complexZ.X q))) := by
  let e₁ := LinearEquiv.ofBijective (hypMap φ m ((HomologicalComplex.single _
    (ComplexShape.up ℤ) (q : ℤ)).map (D.complexZXIso q).hom)) (bijective_hyp_map_of_isIso m _)
  obtain ⟨e₂, he₂⟩ := exists_addEquiv_hyp_single_pushforward_frobenius φ D.hV (D.K q) (q : ℤ) m
  obtain ⟨h₁, h₂⟩ := finrank_eq_and_finiteDimensional_of_semilinear (fun c : KAct φ => c ^ p)
    (bijective_pow_kAct φ) e₂ he₂
  haveI := h₂ inferInstance
  exact ⟨e₁.finrank_eq.trans h₁, LinearEquiv.finiteDimensional e₁.symm⟩

open Module in
/-- **The decomposition on hypercohomology**: `dim ℍ^m(F_*K^•) = ∑_{q ≤ n} dim ℍ^m(K^q[-q])`,
read off from the Čech quasi-isomorphisms `⨁_q K^q[-q] ⟶ Tot Č(𝒰, F_*K^•) ⟵ F_*K^•` built from
local Frobenius splittings. -/
private theorem finrank_hyp_complexZ {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectField k] {n : ℕ}
    {f : X ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f] {ι : Type*} [Fintype ι]
    [HasDerivedCategory.{u} X.Modules] (D : FrobeniusSplittingData p k n f ι)
    (hfin : ∀ (q : Fin (n + 1)) (m : ℤ), FiniteDimensional (KAct φ)
      ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) ((q : ℕ) : ℤ)).obj
        (D.K q))))
    (m : ℤ) :
    finrank (KAct φ) ((hyp X m).obj D.complexZ) = ∑ q : Fin (n + 1), finrank (KAct φ)
      ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) ((q : ℕ) : ℤ)).obj
        (D.K q))) := by
  obtain ⟨L⟩ := D.nonempty_localFrobeniusSplitting
  have hc : ∀ q : Fin n, ∃ c : ℕ, c * ((q : ℕ) + 1).factorial % p = 1 := fun q ↦ by
    have hp : Nat.Coprime p ((q : ℕ) + 1).factorial := by
      rw [Nat.Prime.coprime_iff_not_dvd Fact.out, Nat.Prime.dvd_factorial Fact.out]
      have := D.hpn
      omega
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hp.symm (Fact.out : p.Prime).one_lt
    exact ⟨c, by rwa [mul_comm]⟩
  choose c hc using hc
  let Ψ : ∀ q : Fin (n + 1), CechCocycleData L.U D.complexZ (D.K q) ((q : ℕ) : ℤ) :=
    Fin.cases (D.zeroCocycle L.U D.frobeniusPow D.cartierRep_frobeniusPow)
      (fun q ↦ L.cupCocycle q (c q))
  have hΨ : ∀ q : Fin (n + 1), D.IsCartierCocycle (q : ℕ) (Ψ q) := fun q => by
    refine Fin.cases ?_ (fun q ↦ ?_) q
    · exact D.isCartierCocycle_zeroCocycle L.U D.frobeniusPow D.cartierRep_frobeniusPow L.iSup_U
    · exact L.isCartierCocycle_cupCocycle q (hc q)
  let F : Fin (n + 1) → CochainComplex X.Modules ℤ := fun q =>
    (HomologicalComplex.single _ (ComplexShape.up ℤ) ((q : ℕ) : ℤ)).obj (D.K q)
  let θ : ∀ q, F q ⟶ cechTotal L.U D.complexZ := fun q => (Ψ q).cechMap 0
  haveI hq : QuasiIso (toCechTotal L.U D.complexZ) := quasiIso_toCechTotal L.iSup_U _ 0
  haveI hθ : QuasiIso (biproduct.desc θ) := by
    rw [quasiIso_iff]
    intro m
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hm : ∃ q : Fin (n + 1), ((q : ℕ) : ℤ) = m
    · obtain ⟨q, rfl⟩ := hm
      refine isIso_homologyMap_biproduct_desc F θ _ q (fun j hj => ?_) ?_
      · exact HomologicalComplex.isZero_single_obj_homology _ _ _ _
          (fun h => hj (Fin.ext (by exact_mod_cast h.symm)))
      · have h := D.isIso_homologyMap_of_isCartierCocycle L.iSup_U (Ψ q) (hΨ q)
        have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal L.U D.complexZ)
            ((q : ℕ) : ℤ)) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.quasiIsoAt _)
        simp only [CechCocycleData.homologyMap] at h
        have h' := IsIso.of_isIso_comp_left
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) ((q : ℕ) : ℤ)
            (D.K q)).inv
          (HomologicalComplex.homologyMap ((Ψ q).cechMap 0) ((q : ℕ) : ℤ) ≫
            inv (HomologicalComplex.homologyMap (toCechTotal L.U D.complexZ) ((q : ℕ) : ℤ)))
        exact IsIso.of_isIso_comp_right _ (inv (HomologicalComplex.homologyMap
          (toCechTotal L.U D.complexZ) ((q : ℕ) : ℤ)))
    · push Not at hm
      refine isIso_homologyMap_biproduct_desc_of_isZero F θ _ (fun q => ?_) ?_
      · exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ (fun h => hm q h.symm)
      · have hH : IsIso (HomologicalComplex.homologyMap (toCechTotal L.U D.complexZ) m) :=
          (quasiIsoAt_iff_isIso_homologyMap _ _).1 (hq.quasiIsoAt _)
        refine (HomologicalComplex.ExactAt.of_isZero (isZero_complexZ_X D m ?_)).isZero_homology.of_iso
          (asIso (HomologicalComplex.homologyMap (toCechTotal L.U D.complexZ) m)).symm
        by_contra hcon
        push Not at hcon
        obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j := ⟨m.toNat, by omega⟩
        exact hm ⟨j, by omega⟩ rfl
  have hB : ∀ p < 0, IsZero ((⨁ F).X p) := fun p hp => isZero_biproduct_X F p fun q =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hČ : ∀ p < 0, IsZero ((cechTotal L.U D.complexZ).X p) := fun p hp => by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex₂.total.hom_ext _ fun i₁ i₂ h => ?_
    have h' : i₁ + i₂ = p := h
    rcases lt_or_ge i₁ 0 with h₁ | h₁
    · exact (isZero_cechBicomplex_X_X (a := 0) h₁ i₂).eq_of_src _ _
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change (i : ℤ) = i₂ at hi
        omega)).eq_of_src _ _
  let e₁ := LinearEquiv.ofBijective (hypMap φ m (toCechTotal L.U D.complexZ))
    (bijective_hyp_map_of_quasiIso m _ (fun p hp => isZero_complexZ_X D p (Or.inl hp)) hČ)
  let e₂ := LinearEquiv.ofBijective (hypMap φ m (biproduct.desc θ))
    (bijective_hyp_map_of_quasiIso m _ hB hČ)
  let e₃ := LinearEquiv.ofBijective _ (bijective_hypMap_pi φ F m)
  haveI := fun q => hfin q m
  rw [e₁.finrank_eq, ← e₂.finrank_eq, e₃.finrank_eq, Module.finrank_pi_fintype]

/-- The total complex commutes with the shift of the first index. -/
private noncomputable def totalShiftIso (n : ℤ) :
    HomologicalComplex₂.shiftFunctor₁ AddCommGrpCat.{u} n ⋙
        HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (c₁₂ := ComplexShape.up ℤ) ≅
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (c₁₂ := ComplexShape.up ℤ) ⋙ shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n :=
  NatIso.ofComponents (fun K => K.totalShift₁Iso n)
    (fun f => HomologicalComplex₂.totalShift₁Iso_hom_naturality f n)

private noncomputable def toSheafComplexShiftIso (n : ℤ) :
    shiftFunctor (CochainComplex X.Modules ℤ) n ⋙ toSheafComplex X ≅
      toSheafComplex X ⋙ shiftFunctor _ n :=
  (toSheafX X).mapCochainComplexShiftIso n

private noncomputable def godementSectionsShiftIso (n : ℤ) :
    shiftFunctor (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) ℤ) n ⋙
        (godementSections X.toTopCat).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (godementSections X.toTopCat).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.shiftFunctor₁ AddCommGrpCat.{u} n :=
  (godementSections X.toTopCat).mapCochainComplexShiftIso n

/-- The total complex of Godement sections commutes with shifts. -/
private noncomputable def totComplexShiftIso (n : ℤ) :
    shiftFunctor (CochainComplex X.Modules ℤ) n ⋙ totComplex X ≅
      totComplex X ⋙ shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) n :=
  let A := toSheafComplex X
  let B := (godementSections X.toTopCat).mapHomologicalComplex (ComplexShape.up ℤ)
  let C := HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (c₁₂ := ComplexShape.up ℤ)
  (Functor.associator (shiftFunctor (CochainComplex X.Modules ℤ) n) A (B ⋙ C)).symm ≪≫
    Functor.isoWhiskerRight (toSheafComplexShiftIso n) (B ⋙ C) ≪≫
    Functor.associator A (shiftFunctor _ n) (B ⋙ C) ≪≫
    Functor.isoWhiskerLeft A
      ((Functor.associator (shiftFunctor _ n) B C).symm ≪≫
        Functor.isoWhiskerRight (godementSectionsShiftIso n) C ≪≫
        Functor.associator B (HomologicalComplex₂.shiftFunctor₁ AddCommGrpCat.{u} n) C ≪≫
        Functor.isoWhiskerLeft B (totalShiftIso n) ≪≫
        (Functor.associator B C (shiftFunctor _ n)).symm) ≪≫
    (Functor.associator A (B ⋙ C) (shiftFunctor _ n)).symm

/-- **Hypercohomology commutes with shifts**: `ℍ^a(K[n]) ≅ ℍ^{n + a}(K)`, naturally in `K`. -/
private noncomputable def hypShiftIso (n a : ℤ) :
    shiftFunctor (CochainComplex X.Modules ℤ) n ⋙ hyp X a ≅ hyp X (n + a) :=
  Functor.isoWhiskerRight (totComplexShiftIso n) (HomologicalComplex.homologyFunctor _ _ a) ≪≫
    Functor.isoWhiskerLeft (totComplex X)
      (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u} n a (n + a) rfl)

private lemma smulComplex_shift (s : Γ(X, ⊤)) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (shiftFunctor (CochainComplex X.Modules ℤ) n).map (smulComplex s K) =
      smulComplex s ((shiftFunctor (CochainComplex X.Modules ℤ) n).obj K) := by
  ext i : 1
  rfl

/-- `ℍ^m(M[-q]) ≃ ℍ^{m - q}(M)`, `k`-linearly. -/
private theorem nonempty_linearEquiv_hyp_single (M : X.Modules) (q m : ℤ) :
    Nonempty ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) ≃ₗ[KAct φ]
      (hyp X (-q + m)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)) := by
  let K := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M
  let e₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M ≅
      (shiftFunctor (CochainComplex X.Modules ℤ) (-q)).obj K :=
    (((CochainComplex.singleFunctors X.Modules).shiftIso (-q) q 0 (by omega)).app M).symm
  let L₁ := LinearEquiv.ofBijective (hypMap φ m e₀.hom) (bijective_hyp_map_of_isIso m _)
  let Θ := (hypShiftIso (-q) m).app K
  let L₂ : (hyp X m).obj ((shiftFunctor (CochainComplex X.Modules ℤ) (-q)).obj K) ≃ₗ[KAct φ]
      (hyp X (-q + m)).obj K :=
    { toFun := Θ.hom
      invFun := Θ.inv
      map_add' := map_add _
      map_smul' := fun c x => by
        have h := (hypShiftIso (X := X) (-q) m).hom.naturality (smulComplex (KAct.toΓ φ c) K)
        rw [Functor.comp_map, smulComplex_shift] at h
        exact ConcreteCategory.congr_hom h x
      left_inv := fun x => by
        change (Θ.hom ≫ Θ.inv) x = x
        rw [Θ.hom_inv_id]
        rfl
      right_inv := fun x => by
        change (Θ.inv ≫ Θ.hom) x = x
        rw [Θ.inv_hom_id]
        rfl }
  exact ⟨L₁.trans L₂⟩

/-- Multiplication by a global function on a complex of sheaves of modules (over the structure
sheaf, viewed as sheaves of modules over a sheaf of rings). -/
private noncomputable def smulComplexS (s : Γ(X, ⊤)) {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (SheafOfModules.{u} X.ringCatSheaf) c) : K ⟶ K where
  f i := smulHom s (K.X i)
  comm' i j _ := smulHom_naturality s (K.d i j)

private lemma isZero_hyp_single_zero_of_neg (M : X.Modules) {j : ℤ} (hj : j < 0) :
    IsZero ((hyp X j).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)) := by
  refine (HomologicalComplex.ExactAt.of_isZero ?_).isZero_homology
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex₂.total.hom_ext _ fun i₁ i₂ h => ?_
  have h' : i₁ + i₂ = j := h
  by_cases hi : i₁ = 0
  · subst hi
    exact (isZero_godementSections_X_of_neg X.toTopCat _ (by omega)).eq_of_src _ _
  · exact ((HomologicalComplex.eval _ _ i₂).map_isZero ((godementSections X.toTopCat).map_isZero
      ((toSheafX X).map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)))).eq_of_src _ _

section ComparisonNaturality

open TopologicalSpace

/-- Five commuting squares compose to a commuting rectangle. -/
private lemma comp_five_comm {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    {a₀ : A₀ ⟶ A₀} {a₁ : A₁ ⟶ A₁} {a₂ : A₂ ⟶ A₂} {a₃ : A₃ ⟶ A₃} {a₄ : A₄ ⟶ A₄} {a₅ : A₅ ⟶ A₅}
    {f₁ : A₀ ⟶ A₁} {f₂ : A₁ ⟶ A₂} {f₃ : A₂ ⟶ A₃} {f₄ : A₃ ⟶ A₄} {f₅ : A₄ ⟶ A₅}
    (h₁ : a₀ ≫ f₁ = f₁ ≫ a₁) (h₂ : a₁ ≫ f₂ = f₂ ≫ a₂) (h₃ : a₂ ≫ f₃ = f₃ ≫ a₃)
    (h₄ : a₃ ≫ f₄ = f₄ ≫ a₄) (h₅ : a₄ ≫ f₅ = f₅ ≫ a₅) :
    a₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅) ≫ a₅ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]
  simp only [Category.assoc]

/-- The image under a functor of a natural isomorphism is natural. -/
private lemma map_comp_mapIso_app_hom {C D D' E B : Type*} [Category C] [Category D] [Category D']
    [Category E] [Category B] {S : C ⥤ D} {F' : D ⥤ D'} {Φ : C ⥤ B} {S'' : B ⥤ D'}
    (σ : S ⋙ F' ≅ Φ ⋙ S'') (H : D' ⥤ E) {M N : C} (g : M ⟶ N) :
    H.map (F'.map (S.map g)) ≫ (H.mapIso (σ.app N)).hom =
      (H.mapIso (σ.app M)).hom ≫ H.map (S''.map (Φ.map g)) := by
  simp only [Functor.mapIso_hom, Iso.app_hom, ← H.map_comp]
  exact congrArg H.map (σ.hom.naturality g)

/-- The comparison `ℍ^n(T, F[0]) ≅ H^n(T, F)` of the sheaf cohomology toolkit is natural. -/
private lemma sheafCohomologyIso_naturality {T : TopCat.{u}} {n : ℕ}
    (E : sheafCohomology T n ≅ (globalSections T).rightDerived n)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (g : F ⟶ G) :
    (hypercohomology T n).map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map g) ≫
        (E.app G).hom = (E.app F).hom ≫ ((globalSections T).rightDerived n).map g :=
  E.hom.naturality g

/-- A natural isomorphism, inverted, is natural. -/
private lemma iso_symm_app_hom_naturality {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {M N : C} (g : M ⟶ N) :
    G.map g ≫ (e.symm.app N).hom = (e.symm.app M).hom ≫ F.map g :=
  e.inv.naturality g

/-- Forgetting the module structure on the global sections of an injective resolution commutes
with homology, compatibly with multiplication by a global function. -/
private lemma mapHomologyIso_hom_smulComplexS_naturality {M : X.Modules}
    (I : InjectiveResolution (C := SheafOfModules.{u} X.ringCatSheaf) M) (s : Γ(X, ⊤)) (n : ℕ) :
    ((SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op ⊤)).mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map
        (smulComplexS s I.cocomplex) ≫
      (((((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapHomologicalComplex
        _).obj I.cocomplex).sc n).mapHomologyIso
          (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u})).hom =
      (((((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapHomologicalComplex
        _).obj I.cocomplex).sc n).mapHomologyIso
          (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap
            (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapHomologicalComplex
              _).map (smulComplexS s I.cocomplex)) n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapHomologicalComplex _).map
        (smulComplexS s I.cocomplex)))
    (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u})

/-- On the homology of the global sections of an injective resolution, multiplication by a global
function is multiplication by that element of the ring of global sections. -/
private lemma homologyMap_evaluation_smulComplexS {M : X.Modules}
    (I : InjectiveResolution (C := SheafOfModules.{u} X.ringCatSheaf) M) (s : Γ(X, ⊤)) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapHomologicalComplex
          _).map (smulComplexS s I.cocomplex)) n =
      smulCentral (R := X.ringCatSheaf.obj.obj (op ⊤)) s (fun r => @mul_comm Γ(X, ⊤) _ s r) _ := by
  refine homologyMap_eq_smulCentral (R := X.ringCatSheaf.obj.obj (op ⊤)) s
    (fun r => @mul_comm Γ(X, ⊤) _ s r) _ _ (fun i => ?_) n
  ext y
  have hres : (show X.ringCatSheaf.obj.obj (op ⊤) from
      X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s) = s := by
    change X.presheaf.map _ _ = s
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, X.presheaf.map_id]
    rfl
  exact congrArg (fun r : X.ringCatSheaf.obj.obj (op ⊤) => r • y) hres

/-- Forgetting the module structure, an isomorphism of modules commutes with multiplication by a
central element. -/
private lemma forget₂_map_smulCentral_naturality {R : Type u} [Ring R] (s : R)
    (hs : ∀ r : R, s * r = r * s) {A B : ModuleCat.{u} R} (e : A ≅ B) (φ : B ⟶ B)
    (hφ : φ = smulCentral s hs B) :
    (forget₂ (ModuleCat R) AddCommGrpCat.{u}).map φ ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat.{u}).mapIso e.symm).hom =
      ((forget₂ (ModuleCat R) AddCommGrpCat.{u}).mapIso e.symm).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat.{u}).map (smulCentral s hs A) := by
  rw [hφ, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp, Iso.symm_hom,
    smulCentral_naturality]

end ComparisonNaturality

open TopologicalSpace in
/-- **Godement cohomology of an `𝒪_X`-module is its derived functor cohomology.** For a
`k`-scheme `f : X ⟶ Spec k` and an `𝒪_X`-module `M`, the Godement cohomology `H^q(X, M)` of the
underlying sheaf of abelian groups is additively isomorphic to `cohomologyOverField k f M q`,
and the isomorphism carries the map induced by multiplication by `c ∈ k` on `M` to the
scalar action of `c`. So the `k`-structure on `H^q(X, M)` given by these maps is that of
`cohomologyOverField`. -/
theorem _root_.MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField
    (f : X ⟶ Spec (.of k)) (M : X.Modules) (q : ℕ) :
    ∃ e : (MMP.Analytic.sheafCohomology X.toTopCat q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≃+ cohomologyOverField k f M q,
      ∀ (c : k) x, e ((MMP.Analytic.sheafCohomology X.toTopCat q).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (Stacks.Perfect.FractionClass.smulHom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) M)) x) =
          c • e x := by
  obtain ⟨E, -⟩ := (MMP.Analytic.sheafCohomology_toolkit.{u, 0, 0, 0, 0} X.toTopCat).2.2.1.1
  obtain ⟨-, -, hU⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (Opens.grothendieckTopology X) X.ringCatSheaf
  obtain ⟨eU, -⟩ := hU ⊤
  let R' := X.ringCatSheaf.obj.obj (op ⊤)
  let F₁ := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
  let F₂ := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let I : InjectiveResolution (C := SheafOfModules.{u} X.ringCatSheaf) M := injectiveResolution M
  let Θ := (E X.toTopCat q).app ((toSheafX X).obj M) ≪≫ (eU q).symm.app M ≪≫
    I.isoRightDerivedObj F₁ q ≪≫
    (((F₂.mapHomologicalComplex _).obj I.cocomplex).sc q).mapHomologyIso
      (forget₂ (ModuleCat R') AddCommGrpCat.{u}) ≪≫
    (forget₂ (ModuleCat R') AddCommGrpCat.{u}).mapIso (I.isoRightDerivedObj F₂ q).symm
  refine ⟨Θ.addCommGroupIsoToAddEquiv, fun c x => ?_⟩
  set s := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c
  have hs : (SheafOfModules.toSheaf X.ringCatSheaf).map (Stacks.Perfect.FractionClass.smulHom s M) =
      (toSheafX X).map (smulHom s M) :=
    congrArg (toSheafX X).map (by ext W x; rfl)
  have hk := comp_five_comm
    (sheafCohomologyIso_naturality (E X.toTopCat q) ((toSheafX X).map (smulHom s M)))
    (iso_symm_app_hom_naturality (eU q) (smulHom s M))
    (InjectiveResolution.isoRightDerivedObj_hom_naturality (smulHom s M) I I
      (smulComplexS s I.cocomplex) (smulHom_naturality _ (I.ι.f 0)).symm F₁ q)
    (mapHomologyIso_hom_smulComplexS_naturality I s q)
    (forget₂_map_smulCentral_naturality _ _ (I.isoRightDerivedObj F₂ q) _
      (homologyMap_evaluation_smulComplexS I s q))
  rw [hs]
  exact ConcreteCategory.congr_hom hk x

open TopologicalSpace in
/-- **The Godement cohomology of a coherent module on a proper `k`-scheme is finite-dimensional**:
`ℍ^j(M[0])` is identified with `H^j(X, M)`, and through
`MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField`, compatibly with the action
of `k`, with the derived functor cohomology `cohomologyOverField`. -/
private theorem finiteDimensional_hyp_single_zero {f : X ⟶ Spec (.of k)} [IsProper f]
    (M : X.Modules) [M.IsCoherent] (j : ℤ) :
    FiniteDimensional (KAct ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom)
      ((hyp X j).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)) := by
  set φk : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  rcases lt_or_ge j 0 with hj | hj
  · haveI := AddCommGrpCat.isZero_iff_subsingleton.mp (isZero_hyp_single_zero_of_neg M hj)
    exact Module.Finite.of_finite
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' := ⟨j.toNat, by omega⟩
  obtain ⟨e₀, he₀⟩ := MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField f M j'
  let σ₀ := HomologicalComplex.singleMapHomologicalComplex (toSheafX X) (ComplexShape.up ℤ) 0
  let θ := (hypercohomology X.toTopCat j').mapIso (σ₀.app M)
  let e : (hyp X j').obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) ≃+
      cohomologyOverField k f M j' := θ.addCommGroupIsoToAddEquiv.trans e₀
  letI : Module (KAct φk) (cohomologyOverField k f M j') :=
    (inferInstance : Module k (cohomologyOverField k f M j'))
  have he : ∀ (c : KAct φk) x, e (c • x) = id c • e x := fun c x => by
    have hθ := map_comp_mapIso_app_hom σ₀ (hypercohomology X.toTopCat j')
      (smulHom (KAct.toΓ φk c) M)
    have hx : c • x = (hypercohomology X.toTopCat j').map ((toSheafComplex X).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (smulHom (KAct.toΓ φk c) M))) x := by
      rw [hyp_smul_def, smulComplex_single]
      rfl
    rw [hx]
    exact (congrArg e₀ (ConcreteCategory.congr_hom hθ x)).trans (he₀ c (θ.hom x))
  obtain ⟨-, h⟩ := finrank_eq_and_finiteDimensional_of_semilinear id Function.bijective_id e he
  exact h (finiteDimensional_cohomologyOverField_of_isProper k f M j')

/-- **Hypercohomology of a coherent module on a proper `k`-scheme, placed in one degree, is
finite-dimensional.** -/
private theorem finiteDimensional_hyp_single_of_isCoherent {f : X ⟶ Spec (.of k)} [IsProper f]
    (M : X.Modules) [M.IsCoherent] (q m : ℤ) :
    FiniteDimensional (KAct ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom)
      ((hyp X m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M)) := by
  obtain ⟨L⟩ := nonempty_linearEquiv_hyp_single
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom M q m
  haveI := finiteDimensional_hyp_single_zero (f := f) M (-q + m)
  exact LinearEquiv.finiteDimensional L.symm

section FiniteGeneration

/-- Wedges of vectors lying in the span of `G` lie in the span of the wedges of elements of `G`. -/
private lemma ιMulti_mem_span_of_forall_mem_span {B L M : Type*} [CommRing B] [CommRing L]
    [Algebra B L] [AddCommGroup M] [Module L M] [Module B M] [IsScalarTower B L M]
    (G : Set M) (q : ℕ) (v : Fin q → M) (hv : ∀ m, v m ∈ Submodule.span B G) :
    ExteriorAlgebra.ιMulti L q v ∈ Submodule.span B
      (ExteriorAlgebra.ιMulti L q '' Set.pi Set.univ (fun _ => G)) := by
  classical
  let F := (ExteriorAlgebra.ιMulti L q : M [⋀^Fin q]→ₗ[L] ExteriorAlgebra L M).toMultilinearMap
  suffices key : ∀ s : Finset (Fin q), ∀ w : Fin q → M, (∀ m ∉ s, w m ∈ G) →
      (∀ m ∈ s, w m ∈ Submodule.span B G) →
        F w ∈ Submodule.span B (ExteriorAlgebra.ιMulti L q '' Set.pi Set.univ (fun _ => G)) from
    key Finset.univ v (fun m hm => absurd (Finset.mem_univ m) hm) (fun m _ => hv m)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro w hw _
    exact Submodule.subset_span ⟨w, fun m _ => hw m (Finset.notMem_empty m), rfl⟩
  | insert a s ha ih =>
    intro w hw hs
    have key : ∀ x ∈ Submodule.span B G, F (Function.update w a x) ∈
        Submodule.span B (ExteriorAlgebra.ιMulti L q '' Set.pi Set.univ (fun _ => G)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun m hm => ?_) (fun m hm => ?_)
        · by_cases hma : m = a
          · subst hma
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hma]
            exact hw m (fun h => (Finset.mem_insert.1 h).elim hma hm)
        · have hma : m ≠ a := fun h => ha (h ▸ hm)
          rw [Function.update_of_ne hma]
          exact hs m (Finset.mem_insert_of_mem hm)
      | zero =>
        rw [F.map_update_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [F.map_update_add]
        exact add_mem hx hy
      | smul b x _ hx =>
        rw [← algebraMap_smul L b x, F.map_update_smul, algebraMap_smul]
        exact Submodule.smul_mem _ _ hx
    simpa only [Function.update_eq_self] using key (w a) (hs a (Finset.mem_insert_self a s))

/-- The differential of an element of `B` is a `B`-combination of the differentials of algebra
generators of `B`. -/
private lemma D_algebraMap_mem_span {k B L : Type*} [Field k] [CommRing B] [CommRing L]
    [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L] (s : Set B)
    (hs : Algebra.adjoin k s = ⊤) (b : B) :
    KaehlerDifferential.D k L (algebraMap B L b) ∈
      Submodule.span B ((fun x => KaehlerDifferential.D k L (algebraMap B L x)) '' s) := by
  have hb : b ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap c =>
    rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul, Derivation.leibniz, algebraMap_smul, algebraMap_smul]
    exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)

end FiniteGeneration

section Coherence

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange KaehlerDifferential

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type*} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- A principal ideal sheaf on an affine open stays principal on its basic opens. -/
private lemma ideal_affineBasicOpen_eq_span (J : V.IdealSheafData) (W : V.affineOpens)
    (t : Γ(V, W)) (h : J.ideal W = Ideal.span {t}) (a : Γ(V, W)) :
    J.ideal (V.affineBasicOpen a) =
      Ideal.span {V.presheaf.map (homOfLE (V.basicOpen_le a)).op t} := by
  rw [← J.map_ideal_basicOpen W a, h, Ideal.map_span, Set.image_singleton]

set_option maxRecDepth 8000 in
/-- **The logarithmic forms are quasi-coherent on a chart**: on an affine open `W` on which each
`J j` is principal, the sections of `K q` over a basic open `D(a)` are the localization of those
over `W`. -/
private theorem isLocalizedModule_restrictₗ_K (q : ℕ) (W : V.affineOpens) (t : ι → Γ(V, W))
    (hideal : ∀ j, (D.J j).ideal W = Ideal.span {t j}) (a : Γ(V, W)) :
    letI := moduleOfLE (D.K q) (V.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (D.K q) (V.basicOpen_le a)) := by
  letI := moduleOfLE (D.K q) (V.basicOpen_le a)
  set W' : V.affineOpens := V.affineBasicOpen a with hW'
  have hW'W : (W' : V.Opens) ≤ W := V.basicOpen_le a
  let t' : ι → Γ(V, W') := fun j => V.presheaf.map (homOfLE hW'W).op (t j)
  have hideal' : ∀ j, (D.J j).ideal W' = Ideal.span {t' j} := fun j =>
    ideal_affineBasicOpen_eq_span _ W (t j) (hideal j) a
  have hWU := inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W t hideal
  have hW'U := inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W' t' hideal'
  let WU : V.affineOpens := ⟨(W : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _ hWU⟩
  let W'U : V.affineOpens := ⟨(W' : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _ hW'U⟩
  have hle : (W'U : V.Opens) ≤ WU := inf_le_inf_right _ hW'W
  let aL : Γ(V, WU) := V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op a
  have hbo : (W'U : V.Opens) = V.basicOpen aL := by
    rw [Scheme.basicOpen_res]
    change (V.basicOpen a : V.Opens) ⊓ D.U = ((W : V.Opens) ⊓ D.U) ⊓ V.basicOpen a
    rw [inf_right_comm, inf_eq_right.2 (V.basicOpen_le a)]
  letI := MMP.Mori.sectionAlgebra f WU
  letI := MMP.Mori.sectionAlgebra f W'U
  letI : Algebra Γ(V, WU) Γ(V, W'U) := (V.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hle
  haveI : IsLocalization.Away aL Γ(V, W'U) := isLocalization_away_of_eq_basicOpen aL hbo hle
  refine ⟨fun c => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
  · obtain ⟨_, m, rfl⟩ := c
    change IsUnit (algebraMap Γ(V, W) (Module.End Γ(V, W) Γ(D.K q, V.basicOpen a)) (a ^ m))
    rw [map_pow]
    refine IsUnit.pow m ?_
    obtain ⟨u, hu⟩ := isUnit_map_of_le_basicOpen (V.basicOpen_le a) a le_rfl
    rw [Module.End.isUnit_iff]
    have hact : ∀ x : Γ(D.K q, V.basicOpen a),
        algebraMap Γ(V, W) (Module.End Γ(V, W) Γ(D.K q, V.basicOpen a)) a x =
          (u : Γ(V, V.basicOpen a)) • x := fun x => by
      rw [Module.algebraMap_end_apply]
      change (V.presheaf.map (homOfLE (V.basicOpen_le a)).op a) • x = _
      rw [← hu]
    refine ⟨fun x₁ x₂ hx => ?_, fun x => ⟨(↑u⁻¹ : Γ(V, V.basicOpen a)) • x, ?_⟩⟩
    · rw [hact, hact] at hx
      have := congrArg (fun z => (↑u⁻¹ : Γ(V, V.basicOpen a)) • z) hx
      simpa only [smul_smul, Units.inv_mul, one_smul] using this
    · rw [hact, smul_smul, Units.mul_inv, one_smul]
  · letI : Algebra Γ(V, W) Γ(V, WU) :=
      (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op).hom.toAlgebra
    letI : Algebra Γ(V, W) Γ(V, W') := (V.presheaf.map (homOfLE hW'W).op).hom.toAlgebra
    letI : Algebra Γ(V, W') Γ(V, W'U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ D.U ≤ W')).op).hom.toAlgebra
    haveI : IsLocalization.Away a Γ(V, W') := W.2.isLocalization_basicOpen a
    have hcomm : ∀ b : Γ(V, W), algebraMap Γ(V, WU) Γ(V, W'U) (algebraMap Γ(V, W) Γ(V, WU) b) =
        algebraMap Γ(V, W') Γ(V, W'U) (algebraMap Γ(V, W) Γ(V, W') b) := fun b => by
      change V.presheaf.map _ (V.presheaf.map _ b) = V.presheaf.map _ (V.presheaf.map _ b)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp]
      rfl
    have hunit : ∀ j, IsUnit (algebraMap Γ(V, W) Γ(V, WU) (t j)) := fun j => by
      have hprod : IsUnit (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op
          (∏ j, t j)) := isUnit_map_of_le_basicOpen _ (∏ j, t j) hWU.le
      exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))) hprod
    have hz := (D.mem_range_e_iff W' t' hideal' q (D.e q W' y)).1 ⟨y, rfl⟩
    obtain ⟨N, y₀, hy₀, hN⟩ := exists_pow_smul_eq_mapExteriorPower (A := k) (L := Γ(V, WU))
      (L' := Γ(V, W'U)) hcomm a t hunit _ hz
    have hy₀' := (D.mem_range_e_iff W t hideal q ((formsAlgEquiv f q WU).symm y₀)).2 (by
      rw [LinearEquiv.apply_symm_apply]
      exact hy₀)
    obtain ⟨x₀, hx₀⟩ := hy₀'
    refine ⟨⟨x₀, ⟨a ^ N, Submonoid.pow_mem _ (Submonoid.mem_powers a) N⟩⟩, ?_⟩
    apply D.he_inj q W'
    change D.e q W' ((V.presheaf.map (homOfLE hW'W).op (a ^ N)) •
        (show Γ(D.K q, W') from y)) =
      D.e q W' ((D.K q).presheaf.map (homOfLE hW'W).op x₀)
    rw [D.he_smul, D.he_res, hx₀]
    apply (formsAlgEquiv f q W'U).injective
    have hr : V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ D.U ≤ W')).op
        (V.presheaf.map (homOfLE hW'W).op (a ^ N)) =
        algebraMap Γ(V, W') Γ(V, W'U) (algebraMap Γ(V, W) Γ(V, W') a) ^ N := by
      rw [map_pow, map_pow]
      rfl
    rw [LinearEquiv.map_smul, hr, hN, formsAlgEquiv_restrict f q hle, LinearEquiv.apply_symm_apply]
  · have hsub : (D.K q).presheaf.map (homOfLE (V.basicOpen_le a)).op (x₁ - x₂) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 h
    have hω : (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hle).op
        (D.e q W (x₁ - x₂)) = 0 := by
      have h₁ := D.he_res q (V.basicOpen a) W hW'W (x₁ - x₂)
      rw [hsub, map_zero] at h₁
      exact h₁.symm
    haveI hloc := isLocalizedModule_mapExteriorPower_of_isLocalization (A := k) (L := Γ(V, WU))
      (L' := Γ(V, W'U)) (Submonoid.powers aL) q
    have h1 := formsAlgEquiv_restrict f q hle (D.e q W (x₁ - x₂))
    have h0 := h1.symm.trans ((congrArg (formsAlgEquiv f q W'U) hω).trans
      (LinearEquiv.map_zero (formsAlgEquiv f q W'U)))
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers aL) _).1 h0
    refine ⟨⟨a ^ m, Submonoid.pow_mem _ (Submonoid.mem_powers a) m⟩, ?_⟩
    rw [← sub_eq_zero, ← smul_sub, Submonoid.smul_def]
    apply D.he_inj q W
    rw [D.he_smul]
    refine Eq.trans ?_ (AddMonoidHom.map_zero (D.e q W)).symm
    apply (formsAlgEquiv f q WU).injective
    refine Eq.trans ?_ (LinearEquiv.map_zero (formsAlgEquiv f q WU)).symm
    rw [LinearEquiv.map_smul]
    rw [Submonoid.smul_def] at hm
    refine Eq.trans ?_ hm
    congr 1
    exact map_pow _ a m

set_option maxRecDepth 8000 in
/-- **The logarithmic forms are of finite type on a chart**: their sections over an affine open
on which each `J j` is principal form a finitely generated module. -/
private theorem module_finite_K (q : ℕ) (W : V.affineOpens) (t : ι → Γ(V, W))
    (hideal : ∀ j, (D.J j).ideal W = Ideal.span {t j}) :
    Module.Finite Γ(V, W) Γ(D.K q, W) := by
  have hWU := inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W t hideal
  let WU : V.affineOpens := ⟨(W : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _ hWU⟩
  letI := MMP.Mori.sectionAlgebra f W
  letI := MMP.Mori.sectionAlgebra f WU
  letI : Algebra Γ(V, W) Γ(V, WU) :=
    (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op).hom.toAlgebra
  haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res f
    (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherianRing Γ(V, W) := IsLocallyNoetherian.component_noetherian W
  obtain ⟨s, hs⟩ := (MMP.Mori.finiteType_sectionAlgebra f W.2).out
  let G : Set (Ω[Γ(V, WU)⁄k]) :=
    ((fun x => KaehlerDifferential.D k Γ(V, WU) (algebraMap Γ(V, W) Γ(V, WU) x)) ''
        (s : Set Γ(V, W))) ∪
      Set.range (fun j => Ring.inverse (algebraMap Γ(V, W) Γ(V, WU) (t j)) •
        KaehlerDifferential.D k Γ(V, WU) (algebraMap Γ(V, W) Γ(V, WU) (t j)))
  have hGfin : G.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  let G' := ExteriorAlgebra.ιMulti Γ(V, WU) q '' Set.pi Set.univ (fun _ => G)
  have hG'fin : G'.Finite := (Set.Finite.pi fun _ => hGfin).image _
  have hlog : logForms k Γ(V, WU) t q ≤ Submodule.span Γ(V, W) G' := by
    rw [logForms, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    refine ιMulti_mem_span_of_forall_mem_span G q v (fun m => ?_)
    rcases hv m with ⟨b, hb⟩ | ⟨j, hj⟩
    · rw [← hb]
      exact Submodule.span_mono Set.subset_union_left (D_algebraMap_mem_span _ hs b)
    · rw [← hj]
      exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  have hmem := fun x => (D.mem_range_e_iff W t hideal q (D.e q W x)).1 ⟨x, rfl⟩
  let ψ : Γ(D.K q, W) →ₗ[Γ(V, W)] Submodule.span Γ(V, W) G' :=
    { toFun := fun x => ⟨(formsAlgEquiv f q WU (D.e q W x) :
          ExteriorAlgebra Γ(V, WU) (Ω[Γ(V, WU)⁄k])), hlog (hmem x)⟩
      map_add' := fun x y => by
        ext1
        simp only [map_add, Submodule.coe_add]
      map_smul' := fun b x => by
        ext1
        simp only [RingHom.id_apply, Submodule.coe_smul]
        rw [D.he_smul, LinearEquiv.map_smul, Submodule.coe_smul]
        exact algebraMap_smul Γ(V, WU) b _ }
  have hψ : Function.Injective ψ := fun x y hxy => by
    have h₁ := congrArg Subtype.val hxy
    exact D.he_inj q W ((formsAlgEquiv f q WU).injective (Subtype.val_injective h₁))
  haveI : Module.Finite Γ(V, W) (Submodule.span Γ(V, W) G') := Module.Finite.span_of_finite _ hG'fin
  haveI : IsNoetherian Γ(V, W) (Submodule.span Γ(V, W) G') :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ψ hψ

end Coherence

/-- **The sheaves of logarithmic forms are coherent.** They are quasi-coherent and of finite
type on the charts of the divisor, which cover `V`, and `V` is Noetherian. -/
private theorem isCoherent_K {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectField k] {n : ℕ}
    {f : X ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f] {ι : Type*} [Fintype ι]
    [HasDerivedCategory.{u} X.Modules] (D : FrobeniusSplittingData p k n f ι) (q : ℕ) :
    (D.K q).IsCoherent := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let P : X.Opens → Prop := fun W => ∃ hW : IsAffineOpen W, ∃ t : ι → Γ(X, W),
    ∀ j, (D.J j).ideal ⟨W, hW⟩ = Ideal.span {t j}
  have hcov : ∀ x : X, ∃ W, IsAffineOpen W ∧ P W ∧ x ∈ W := fun x => by
    obtain ⟨W, t, -, hx, hideal, -⟩ :=
      exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU (O := ⊤) (x := x) trivial
    exact ⟨W, W.2, ⟨W.2, t, hideal⟩, hx⟩
  haveI : (D.K q).IsQuasicoherent :=
    isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover (D.K q) P hcov
      (fun W hW ⟨_, t, hideal⟩ a => isLocalizedModule_restrictₗ_K D q ⟨W, hW⟩ t hideal a)
  haveI : (D.K q).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn (D.K q)
      (fun c : {W : X.affineOpens // ∃ t : ι → Γ(X, W), ∀ j, (D.J j).ideal W = Ideal.span {t j}} =>
        (c.1 : X.Opens))
      (TopologicalSpace.IsOpenCover.mk (top_le_iff.mp fun x _ => by
        obtain ⟨W, hW, ⟨_, t, hideal⟩, hx⟩ := hcov x
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, t, hideal⟩, hx⟩))
      (fun c => c.1.2)
      (fun c =>
        Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
          _ c.1 (module_finite_K D q c.1 c.2.choose c.2.choose_spec))
  exact
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **Deligne–Illusie decomposition and degeneration for a lifted simple normal crossing pair.**
Let `k` be a perfect field of characteristic `p`, let `f : V ⟶ Spec k` be smooth and proper of
relative dimension `n < p`, and let the ideal sheaves `Jⱼ` define a simple normal crossing divisor
`S = ∑ⱼ Sⱼ`. Suppose `(V, S)` is the closed fibre of a smooth scheme `𝒱` over `W₂(k)` carrying
a relative simple normal crossing divisor `∑ⱼ 𝒮ⱼ` with `Sⱼ = 𝒮ⱼ ∩ V`. Let `K q`, with the
embeddings `e`, be the sheaf `Ω^q_{V/k}(log S)` of logarithmic `q`-forms, and let `d` be the
logarithmic de Rham differential on the Frobenius pushforwards `F_* K q`, where `F` is the
absolute Frobenius of `V`. Then, in the derived category of `𝒪_V`-modules,
`⨁_{q ≤ n} Ω^q_{V/k}(log S)[-q] ≅ F_*Ω^•_{V/k}(log S)`, and the logarithmic Hodge-to-de Rham
spectral sequence degenerates at `E₁`: for every `i` and `m`, the map
`ℍ^m(V, σ^{≥i}Ω^•_{V/k}(log S)) ⟶ ℍ^m(V, Ω^•_{V/k}(log S))` is injective, `σ^{≥i}` being given
as any complex vanishing below degree `i` with a map to the complex that is an isomorphism from
degree `i` on. -/
@[mmp "lem_mmp_lc_bpf_log_frobenius_splitting"]
public theorem nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift
    (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] [PerfectField k]
    (n : ℕ) (hpn : n < p)
    {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension n f]
    (hV : IsInCharacteristic V p)
    {ι : Type*} [Fintype ι] (J : ι → V.IdealSheafData)
    (hJ : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 k)))
    (I : ι → 𝒱.IdealSheafData)
    (π : TruncatedWittVector p 2 k →+* k) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π)))
    (hIJ : ∀ j, ∃ φ, IsPullback φ (J j).subschemeι (I j).subschemeι i)
    (hI : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, I j).subschemeι ≫ g) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, I j).subscheme))
    [HasDerivedCategory.{u} V.Modules]
    (U : V.Opens) (hU : U = ((⨅ j, J j).support).compl)
    (K : ℕ → V.Modules)
    (e : ∀ (q : ℕ) (W : V.Opens), Γ(K q, W) →+ Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ U))
    (he_inj : ∀ (q : ℕ) W, Function.Injective (e q W))
    (he_smul : ∀ (q : ℕ) W (a : Γ(V, W)) (s : Γ(K q, W)),
      e q W (a • s) = V.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op a • e q W s)
    (he_res : ∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (s : Γ(K q, W₂)),
      e q W₁ ((K q).presheaf.map (homOfLE h).op s) =
        (f.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (inf_le_inf_right _ h)).op (e q W₂ s))
    (he_range : ∀ (q : ℕ) (W : V.Opens) (ω : Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ U)),
      ω ∈ Set.range (e q W) ↔
        ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : ι → Γ(V, W')),
          (∀ j, c j ∈ (J j).ideal W') →
          (∃ η : Γ(f.relativeDifferentialForms (q : ℤ), W'),
            (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op ω) ∧
          (∃ η : Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), W'),
            (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op
                    (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ U)) ω)))
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K (q + 1)))
    (hd : ∀ q : ℕ, d q ≫ d (q + 1) = 0)
    (he_d : ∀ (q : ℕ) (W : V.Opens) (s : Γ(K q, absoluteFrobenius V p hV ⁻¹ᵁ W)),
      e (q + 1) (absoluteFrobenius V p hV ⁻¹ᵁ W) ((d q).app W s) =
        ((f.deRhamComplex).d q (q + 1)).val.app (op (absoluteFrobenius V p hV ⁻¹ᵁ W ⊓ U))
          (e q _ s)) :
    Nonempty ((⨁ fun q : Fin (n + 1) ↦
        (DerivedCategory.singleFunctor V.Modules (q : ℤ)).obj (K q)) ≅
      DerivedCategory.Q.obj ((CochainComplex.of
        (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K q)) d hd).extend
          ComplexShape.embeddingUpNat)) ∧
    ∀ (i : ℕ) (L : CochainComplex V.Modules ℤ)
      (φ : L ⟶ (CochainComplex.of
        (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K q)) d hd).extend
          ComplexShape.embeddingUpNat),
      (∀ m : ℤ, m < i → IsZero (L.X m)) → (∀ m : ℤ, (i : ℤ) ≤ m → IsIso (φ.f m)) →
      ∀ m : ℤ, Function.Injective ((MMP.Analytic.hypercohomology V.toTopCat m).map
        (((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).hom := by
  set D := FrobeniusSplittingData.mk hpn hV J hJ 𝒱 g I π hπ i hi hIJ hI U hU K e he_inj
    he_smul he_res he_range d hd he_d
  refine ⟨D.nonempty_iso_directSum_singleFunctor, ?_⟩
  intro i₀ L ψ hL hψ m
  let φk : k →+* Γ(V, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  have hfinU : ∀ (q : ℕ) (m : ℤ), FiniteDimensional (KAct φk)
      ((hyp V m).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (q : ℤ)).obj (D.K q))) :=
    fun q m => by
      haveI := isCoherent_K D q
      exact finiteDimensional_hyp_single_of_isCoherent (D.K q) q m
  have hdim : ∀ m : ℤ, Module.finrank (KAct φk) ((hyp V m).obj D.complexZ) =
      ∑ q ∈ Finset.range (n + 1), Module.finrank (KAct φk) ((hyp V m).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (q : ℤ)).obj (D.complexZ.X q))) := by
    intro m
    rw [finrank_hyp_complexZ φk D (fun q => hfinU q) m,
      ← Fin.sum_univ_eq_sum_range (fun q => Module.finrank (KAct φk) ((hyp V m).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (q : ℤ)).obj (D.complexZ.X q))))]
    exact Finset.sum_congr rfl fun q _ =>
      (haveI := hfinU q m; finrank_hyp_single_complexZ_X φk D q m).1.symm
  exact injective_hyp_map_of_finrank_eq_sum φk D.complexZ n (isZero_complexZ_X D)
    (fun q m => haveI := hfinU q m; (finrank_hyp_single_complexZ_X φk D q m).2) hdim
    i₀ L ψ hL hψ m

end KModule

end MMP.DeRham
