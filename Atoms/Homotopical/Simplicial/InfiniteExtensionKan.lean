import Atoms.Homotopical.Simplicial.InfiniteExtension

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

theorem sd_map_sd_map_comp_eq_of_nMap {A B : SSet.{u}} [A.Nonsingular] [B.Nonsingular]
    (i : A ⟶ B) [Mono i] (b : (nerve B.N).N →o A.N)
    (hb : ∀ x : (nerve A.N).N, nMap (nerveMap (nMap i).monotone.functor ≫
        (sdIsoNerveN B).inv ≫ lastVertex.app B) x =
      nMap i (b (nMap (nerveMap (nMap i).monotone.functor) x))) :
    SSet.sd.map (SSet.sd.map i) ≫ SSet.sd.map (sdIsoNerveN B).hom ≫
        (sdIsoNerveN (nerve B.N)).hom ≫ nerveMap b.monotone.functor ≫ (sdIsoNerveN A).inv =
      SSet.sd.map (lastVertex.app A) := by
  set Ni := nerveMap (nMap i).monotone.functor
  have e₁ : SSet.sd.map i = (sdIsoNerveN A).hom ≫ Ni ≫ (sdIsoNerveN B).inv := by
    rw [← Category.assoc, ← sd_map_sdIsoNerveN_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have e₂ := sd_map_sdIsoNerveN_hom Ni
  have e₃ := sd_map_sdIsoNerveN_hom (X := nerve A.N) (Y := B)
    (Ni ≫ (sdIsoNerveN B).inv ≫ (lastVertex.app B : SSet.sd.obj B ⟶ B))
  have e₃' : SSet.sd.map (Ni ≫ (sdIsoNerveN B).inv ≫ (lastVertex.app B : SSet.sd.obj B ⟶ B)) =
      ((sdIsoNerveN (nerve A.N)).hom ≫ nerveMap (nMap (Ni ≫ (sdIsoNerveN B).inv ≫
        (lastVertex.app B : SSet.sd.obj B ⟶ B))).monotone.functor) ≫ (sdIsoNerveN B).inv :=
    (Iso.eq_comp_inv _).2 e₃
  have e₄ : nerveMap (nMap Ni).monotone.functor ≫ nerveMap b.monotone.functor ≫ Ni =
      nerveMap (nMap (Ni ≫ (sdIsoNerveN B).inv ≫
        (lastVertex.app B : SSet.sd.obj B ⟶ B))).monotone.functor := by
    ext d x j
    exact (hb (x.obj j)).symm
  have hl : SSet.sd.map (lastVertex.app A) ≫ SSet.sd.map i =
      SSet.sd.map (SSet.sd.map i ≫ lastVertex.app B) := by
    rw [← Functor.map_comp]
    exact congrArg SSet.sd.map (lastVertex.naturality i).symm
  rw [← cancel_mono (SSet.sd.map i), hl]
  calc _ = SSet.sd.map (sdIsoNerveN A).hom ≫ (sdIsoNerveN (nerve A.N)).hom ≫
        (nerveMap (nMap Ni).monotone.functor ≫ nerveMap b.monotone.functor ≫ Ni) ≫
          (sdIsoNerveN B).inv := by
        rw [e₁]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
          Iso.map_inv_hom_id_assoc]
        rw [reassoc_of% e₂]
    _ = SSet.sd.map (sdIsoNerveN A).hom ≫
        SSet.sd.map (Ni ≫ (sdIsoNerveN B).inv ≫ (lastVertex.app B : SSet.sd.obj B ⟶ B)) := by
        rw [e₄, e₃']
        simp only [Category.assoc]
    _ = _ := by
        rw [e₁]
        simp only [Functor.map_comp, Category.assoc]

theorem nVertices_nMap_eq_simplexVertices {Z : SSet.{u}} {m : ℕ} (F : Z ⟶ Δ[m]) (x : Z.N) :
    (nVertices (nMap F x)).1 = simplexVertices (F.app _ x.simplex) := by
  change simplexVertices (x.toS.map F).toN.simplex = _
  rw [← simplexVertices_map_of_epi (x.toS.map F).toNπ, SSet.S.map_toNπ_op_apply]
  rfl

theorem range_nMap_simplex_obj {Z : SSet.{u}} {R : Type u} [PartialOrder R] (F : Z ⟶ nerve R)
    (x : Z.N) :
    Set.range (nMap F x).simplex.obj = Set.range (F.app _ x.simplex).obj := by
  have hs := SSet.S.map_toNπ_op_apply (x.toS.map F)
  have he := SimplexCategory.epi_iff_surjective.1 (inferInstance : Epi (x.toS.map F).toNπ)
  change Set.range (x.toS.map F).toN.simplex.obj = Set.range (x.toS.map F).simplex.obj
  rw [← hs]
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := he j
    exact ⟨i, by rw [← hi]; rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩

theorem sdIsoNerveN_inv_comp_lastVertex_app_apply (m d : ℕ)
    (c : (nerve (Δ[m] : SSet.{u}).N) _⦋d⦌) (j : Fin (d + 1)) :
    (show (Δ[m] : SSet.{u}) _⦋d⦌ from
      ((sdIsoNerveN Δ[m]).inv ≫ lastVertex.app Δ[m]).app _ c) j =
      (chainMax ⦋m⦌ ((chainNOrderIso ⦋m⦌).symm (c.obj j))).down := by
  obtain ⟨u, rfl⟩ : ∃ u, (simplexSdToNerveN.app ⦋m⦌).app _ u = c :=
    ⟨(nerveMap (chainNOrderIso ⦋m⦌).symm.monotone.functor).app _ c,
      nerve.ext_of_isThin (funext fun j ↦ (chainNOrderIso ⦋m⦌).apply_symm_apply _)⟩
  have h₁ : SSet.stdSimplex.sdIso.inv.app ⦋m⦌ ≫ (sdIsoNerveN Δ[m]).hom =
      simplexSdToNerveN.app ⦋m⦌ :=
    sdIso_inv_app_sdToNerveN_app ⦋m⦌
  have key : (SSet.stdSimplex.sdIso.inv.app ⦋m⦌ ≫ (sdIsoNerveN Δ[m]).hom) ≫
      ((sdIsoNerveN Δ[m]).inv ≫ lastVertex.app Δ[m]) = simplexLastVertex.app ⦋m⦌ := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact sdIso_inv_app_lastVertex_app ⦋m⦌
  have e : ((simplexSdToNerveN.app ⦋m⦌).app _ u).obj j = chainNOrderIso ⦋m⦌ (u.obj j) := rfl
  rw [e]
  refine Eq.trans ?_ (congrArg (fun S ↦ (chainMax ⦋m⦌ S).down)
    ((chainNOrderIso ⦋m⦌).symm_apply_apply (u.obj j))).symm
  rw [← h₁]
  exact congrArg (fun φ : _ ⟶ Δ[m] ↦ (show (Δ[m] : SSet.{u}) _⦋d⦌ from φ.app _ u) j) key

namespace KanRetraction

open SdHorn

variable {n : ℕ} (k : Fin (n + 2))

noncomputable def faceMax {m : ℕ} (p : (Δ[m] : SSet.{u}).N) : Fin (m + 1) :=
  (chainMax ⦋m⦌ ((chainNOrderIso ⦋m⦌).symm p)).down

theorem faceMax_mem {m : ℕ} (p : (Δ[m] : SSet.{u}).N) : faceMax p ∈ (nVertices p).1 := by
  have h := nVertices_chainNOrderIso m ((chainNOrderIso ⦋m⦌).symm p)
  rw [OrderIso.apply_symm_apply] at h
  rw [h]
  exact Finset.mem_map.2 ⟨_, Finset.max'_mem _ ((chainNOrderIso ⦋m⦌).symm p).nonempty, rfl⟩

noncomputable def kanVertex (p : (Δ[n + 1] : SSet.{u}).N) : Fin (n + 2) :=
  if insert k (nVertices p).1 ≠ Finset.univ then faceMax p else k

theorem kanVertex_mem (p : (Δ[n + 1] : SSet.{u}).N) :
    kanVertex k p ∈ insert k (nVertices p).1 := by
  unfold kanVertex
  split_ifs
  · exact Finset.mem_insert_of_mem (faceMax_mem p)
  · exact Finset.mem_insert_self _ _

noncomputable def kanFinset (w : (nerve (Δ[n + 1] : SSet.{u}).N).N) : Finset (Fin (n + 2)) :=
  Finset.univ.image (fun j ↦ kanVertex k (w.simplex.obj j))

theorem insert_kanFinset_ne_univ (w : (nerve (Δ[n + 1] : SSet.{u}).N).N) :
    insert k (kanFinset k w) ≠ Finset.univ := by
  let T := w.simplex.obj
  by_cases hΦ : ∃ j, insert k (nVertices (T j)).1 ≠ Finset.univ
  · let J := Finset.univ.filter (fun j ↦ insert k (nVertices (T j)).1 ≠ Finset.univ)
    have hJ : J.Nonempty := by
      obtain ⟨j, hj⟩ := hΦ
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    have hmax := (Finset.mem_filter.1 (J.max'_mem hJ)).2
    obtain ⟨v, hv⟩ : ∃ v, v ∉ insert k (nVertices (T (J.max' hJ))).1 := by
      by_contra h
      push Not at h
      exact hmax (Finset.eq_univ_iff_forall.2 h)
    intro hall
    have hvk : v ≠ k := fun h ↦ hv (h ▸ Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.1 (hall ▸ Finset.mem_univ v) with h | h
    · exact hvk h
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
      by_cases hjΦ : insert k (nVertices (T j)).1 ≠ Finset.univ
      · have hle : j ≤ J.max' hJ := J.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hjΦ⟩)
        have hsub : (nVertices (T j)).1 ⊆ (nVertices (T (J.max' hJ))).1 :=
          (nVertices_le_iff _ _).2 (w.simplex.map (homOfLE hle)).le
        apply hv
        rw [← hj]
        exact Finset.insert_subset_insert k hsub (kanVertex_mem k (T j))
      · apply hvk
        rw [← hj]
        unfold kanVertex
        rw [if_neg hjΦ]
  · push Not at hΦ
    have hsub : kanFinset k w ⊆ {k} := by
      intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
      unfold kanVertex
      rw [if_neg (not_not.2 (hΦ j))]
      exact Finset.mem_singleton_self k
    intro hall
    apply Finset.singleton_ne_univ k
    refine Finset.eq_univ_of_forall (fun v ↦ ?_)
    rcases Finset.mem_insert.1 (hall ▸ Finset.mem_univ v) with rfl | hv
    · exact Finset.mem_singleton_self _
    · exact hsub hv

theorem kanFinset_mono {w w' : (nerve (Δ[n + 1] : SSet.{u}).N).N} (h : w ≤ w') :
    kanFinset k w ⊆ kanFinset k w' := by
  obtain ⟨f, _, hf⟩ := SSet.N.le_iff_exists_mono.1 h
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  refine Finset.mem_image.2 ⟨f.toOrderHom j, Finset.mem_univ _, ?_⟩
  rw [← hf]
  rfl

theorem exists_hornEmbedding_eq (T : Subsets.{u} n) (hT : insert k T.1 ≠ Finset.univ) :
    ∃ y, hornEmbedding k y = T := by
  obtain ⟨y, rfl⟩ := (stdSimplexSubsetsIso n).surjective T
  have hmem := (insert_simplexVertices_ne_univ_iff (k := k) y.simplex).1 hT
  refine ⟨SSet.N.mk (⟨y.simplex, hmem⟩ : (SSet.horn.{u} (n + 1) k : SSet.{u}) _⦋y.dim⦌)
    ((SSet.nonDegenerate_iff_of_mono (SSet.horn.{u} (n + 1) k).ι _).1 y.nonDegenerate), ?_⟩
  change stdSimplexSubsetsIso n (nMap _ _) = _
  rw [nMap_of_mono]
  rfl

noncomputable def kanMap :
    (nerve (Δ[n + 1] : SSet.{u}).N).N →o (SSet.horn.{u} (n + 1) k : SSet.{u}).N where
  toFun w := (exists_hornEmbedding_eq k ⟨kanFinset k w, Finset.univ_nonempty.image _⟩
    (insert_kanFinset_ne_univ k w)).choose
  monotone' w w' h := (hornEmbedding k).le_iff_le.1 (by
    rw [(exists_hornEmbedding_eq k _ (insert_kanFinset_ne_univ k w)).choose_spec,
      (exists_hornEmbedding_eq k _ (insert_kanFinset_ne_univ k w')).choose_spec]
    exact kanFinset_mono k h)

theorem hornEmbedding_kanMap (w : (nerve (Δ[n + 1] : SSet.{u}).N).N) :
    (hornEmbedding k (kanMap k w)).1 = kanFinset k w :=
  congrArg Subsets.val (exists_hornEmbedding_eq k _ (insert_kanFinset_ne_univ k w)).choose_spec

theorem insert_nVertices_nMap_ne_univ (q : (SSet.horn.{u} (n + 1) k : SSet.{u}).N) :
    insert k (nVertices (nMap (SSet.horn.{u} (n + 1) k).ι q)).1 ≠ Finset.univ := by
  change insert k (simplexVertices (nMap (SSet.horn.{u} (n + 1) k).ι q).simplex) ≠ _
  rw [nMap_of_mono]
  exact (insert_simplexVertices_ne_univ_iff (k := k) _).2 q.simplex.2

theorem nMap_comp_lastVertex_app_eq (x : (nerve (SSet.horn.{u} (n + 1) k : SSet.{u}).N).N) :
    nMap (nerveMap (nMap (SSet.horn.{u} (n + 1) k).ι).monotone.functor ≫
        (sdIsoNerveN Δ[n + 1]).inv ≫ lastVertex.app Δ[n + 1]) x =
      nMap (SSet.horn.{u} (n + 1) k).ι
        (kanMap k (nMap (nerveMap (nMap (SSet.horn.{u} (n + 1) k).ι).monotone.functor) x)) := by
  set Ni := nerveMap (nMap (SSet.horn.{u} (n + 1) k).ι).monotone.functor
  apply (stdSimplexNOrderIso (n + 1)).injective
  apply Subtype.ext
  change (nVertices (nMap (Ni ≫ (sdIsoNerveN Δ[n + 1]).inv ≫
    (lastVertex.app Δ[n + 1] : _ ⟶ Δ[n + 1])) x)).1 =
      (hornEmbedding k (kanMap k (nMap Ni x))).1
  rw [hornEmbedding_kanMap, nVertices_nMap_eq_simplexVertices]
  have hr := range_nMap_simplex_obj Ni x
  have hval (i : Fin (x.dim + 1)) :
      (show (Δ[n + 1] : SSet.{u}) _⦋x.dim⦌ from (Ni ≫ (sdIsoNerveN Δ[n + 1]).inv ≫
        (lastVertex.app Δ[n + 1] : _ ⟶ Δ[n + 1])).app _ x.simplex) i =
        kanVertex k (nMap (SSet.horn.{u} (n + 1) k).ι (x.simplex.obj i)) := by
    refine (sdIsoNerveN_inv_comp_lastVertex_app_apply (n + 1) x.dim
      (Ni.app _ x.simplex) i).trans ?_
    unfold kanVertex
    rw [if_pos (insert_nVertices_nMap_ne_univ k _)]
    rfl
  ext v
  rw [mem_simplexVertices]
  simp only [kanFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ : (Ni.app _ x.simplex).obj i ∈ Set.range (nMap Ni x).simplex.obj :=
      hr ▸ ⟨i, rfl⟩
    exact ⟨j, by rw [hval, hj]; rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ : (nMap Ni x).simplex.obj j ∈ Set.range (Ni.app _ x.simplex).obj :=
      hr ▸ ⟨j, rfl⟩
    exact ⟨i, by rw [hval, ← hi]; rfl⟩

end KanRetraction

theorem exists_sd_sd_horn_retraction (n : ℕ) (k : Fin (n + 2)) :
    ∃ ψ : SSet.sd.obj (SSet.sd.obj Δ[n + 1]) ⟶ SSet.sd.obj (SSet.horn.{u} (n + 1) k),
      SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) k).ι) ≫ ψ =
        SSet.sd.map (lastVertex.app (SSet.horn.{u} (n + 1) k)) :=
  ⟨_, sd_map_sd_map_comp_eq_of_nMap (SSet.horn.{u} (n + 1) k).ι (KanRetraction.kanMap k)
    (KanRetraction.nMap_comp_lastVertex_app_eq k)⟩

theorem exists_comp_eq_comp_exUnit_app {A B X : SSet.{u}} (i : A ⟶ B)
    (ψ : SSet.sd.obj (SSet.sd.obj B) ⟶ SSet.sd.obj A)
    (hψ : SSet.sd.map (SSet.sd.map i) ≫ ψ = SSet.sd.map (lastVertex.app A))
    (a : A ⟶ SSet.ex.obj X) :
    ∃ b : B ⟶ SSet.ex.obj (SSet.ex.obj X), i ≫ b = a ≫ exUnit.app (SSet.ex.obj X) := by
  let adj := SSet.sdExAdjunction.{u}
  refine ⟨adj.homEquiv _ _ (adj.homEquiv _ _ (ψ ≫ (adj.homEquiv _ _).symm a)), ?_⟩
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, ← Category.assoc, hψ,
    adj.homEquiv_naturality_left]
  dsimp only [Functor.id_obj]
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right,
    sdExAdjunction_homEquiv_lastVertex_app]
  exact (exUnit.naturality a).symm

theorem exists_fill_exUnit_app {X : SSet.{u}} {n : ℕ} {k : Fin (n + 2)}
    (a : (SSet.horn.{u} (n + 1) k : SSet.{u}) ⟶ SSet.ex.obj X) :
    ∃ b : Δ[n + 1] ⟶ SSet.ex.obj (SSet.ex.obj X),
      (SSet.horn.{u} (n + 1) k).ι ≫ b = a ≫ exUnit.app (SSet.ex.obj X) := by
  obtain ⟨ψ, hψ⟩ := exists_sd_sd_horn_retraction n k
  exact exists_comp_eq_comp_exUnit_app _ ψ hψ a

theorem exists_comp_eq_of_exUnit {A B X : SSet.{u}} [IsFinitelyPresentable.{u} A]
    (i : A ⟶ B)
    (h : ∀ (Z : SSet.{u}) (a : A ⟶ SSet.ex.obj Z),
      ∃ b : B ⟶ SSet.ex.obj (SSet.ex.obj Z), i ≫ b = a ≫ exUnit.app (SSet.ex.obj Z))
    (t : A ⟶ exInfty.{u}.obj X) : ∃ l : B ⟶ exInfty.{u}.obj X, i ≫ l = t := by
  obtain ⟨m, t', rfl⟩ := exists_comp_ι_app_eq t
  let a : A ⟶ SSet.ex.obj ((exTower.{u}.obj m).obj X) :=
    t' ≫ (exTower.{u}.map (homOfLE (Nat.le_add_right m 1))).app X
  obtain ⟨b, hb⟩ := h _ a
  refine ⟨b ≫ (exInftyι.{u} (m + 2)).app X, ?_⟩
  have e : exUnit.app (SSet.ex.obj ((exTower.{u}.obj m).obj X)) =
      (exTower.{u}.map (homOfLE (Nat.le_add_right (m + 1) 1))).app X :=
    (exTower_map_succ_app (m + 1) X).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (exInftyι.{u} (m + 2)).app X) (hb.trans (congrArg (a ≫ ·) e))).trans ?_
  refine ((Category.assoc _ _ _).trans
    (congrArg (a ≫ ·) (exTower_map_app_comp_ι_app _ X))).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (t' ≫ ·) (exTower_map_app_comp_ι_app _ X))

open SSet.modelCategoryQuillen in
instance kanComplex_exInfty (X : SSet.{u}) : SSet.KanComplex (exInfty.{u}.obj X) := by
  refine (HomotopicalAlgebra.isFibrant_iff _).2 ⟨?_⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  refine ⟨fun {t _} _ ↦ ?_⟩
  obtain ⟨l, hl⟩ := exists_comp_eq_of_exUnit _ (fun Z a ↦ exists_fill_exUnit_app a) t
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := by subsingleton }⟩⟩

end Atoms.Homotopical
