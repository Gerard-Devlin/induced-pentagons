import InducedPentagonsPaper.JointFlagGraphs

/-! Transport of joint flag samples, rooted types, and counts through host isomorphisms. -/

namespace InducedPentagons.Paper

namespace JointFlagSample

def map {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : JointFlagSample m roots free :=
  ⟨x.1.trans e.toEmbedding, x.left.image e, by
    constructor
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      apply Finset.mem_compl.mpr
      intro hr
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hr
      have he : x.1 i = u := e.injective hi
      have hu' : u ∈ flagRootVertices x.1 :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩
      exact (Finset.disjoint_left.mp x.roots_left_disjoint) hu' hu
    · rw [Finset.card_image_of_injective _ e.injective, x.left_card]⟩

@[simp] theorem map_left {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : (x.map e).left = x.left.image e := rfl

@[simp] theorem map_root {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) (i : Fin roots) : (x.map e).1 i = e (x.1 i) := rfl

theorem ext {n roots free : Nat} {x y : JointFlagSample n roots free}
    (hf : x.1 = y.1) (hs : x.left = y.left) : x = y := by
  cases x with | mk f x =>
    cases y with | mk g y =>
      dsimp at hf
      subst g
      apply congrArg (Sigma.mk f)
      exact Subtype.ext hs

@[simp] theorem map_symm_map {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : (x.map e).map e.symm = x := by
  apply ext
  · apply Function.Embedding.ext
    intro i
    exact e.symm_apply_apply (x.1 i)
  · ext v
    simp

def mapEquiv {n m roots free : Nat} (e : Fin n ≃ Fin m) :
    JointFlagSample n roots free ≃ JointFlagSample m roots free where
  toFun := map e
  invFun := map e.symm
  left_inv := map_symm_map e
  right_inv := map_symm_map e.symm

theorem map_right {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : (x.map e).right = x.right.image e := by
  ext v
  obtain ⟨u, rfl⟩ := e.surjective v
  simp only [right, Finset.mem_compl, Finset.mem_union, map_left]
  have hroot : e u ∈ flagRootVertices (x.map e).1 ↔ u ∈ flagRootVertices x.1 := by
    simp only [flagRootVertices, Finset.mem_image, Finset.mem_univ, true_and, map_root]
    simp only [e.injective.eq_iff]
  rw [hroot]
  simp only [Finset.mem_image, e.injective.eq_iff, exists_eq_right, Finset.mem_compl,
    Finset.mem_union]

theorem map_swap {n m roots free : Nat} (hn : n = roots + 2 * free)
    (hm : m = roots + 2 * free) (e : Fin n ≃ Fin m) (x : JointFlagSample n roots free) :
    (x.swap hn).map e = (x.map e).swap hm := by
  apply ext
  · rfl
  · exact (map_right e x).symm

def freeMapEquiv {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : Fin free ≃ Fin free :=
  (x.left.orderIsoOfFin x.left_card).toEquiv |>.trans
    ((Equiv.subtypeEquiv e (fun v => by simp)).trans
      ((x.map e).left.orderIsoOfFin (x.map e).left_card).toEquiv.symm)

theorem subsetVertex_freeMapEquiv {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) (i : Fin free) :
    subsetVertex (x.map e).left (x.map e).left_card (freeMapEquiv e x i) =
      e (subsetVertex x.left x.left_card i) := by
  simp only [subsetVertex_eq_orderEmb]
  change (((x.map e).left.orderIsoOfFin (x.map e).left_card)
    (freeMapEquiv e x i)).val = e (((x.left.orderIsoOfFin x.left_card) i).val)
  unfold freeMapEquiv
  change (((x.map e).left.orderIsoOfFin (x.map e).left_card).toEquiv
    (((x.map e).left.orderIsoOfFin (x.map e).left_card).toEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

def vertexMapEquiv {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) : Fin (roots + free) ≃ Fin (roots + free) where
  toFun := Fin.addCases (fun i => i.castAdd free)
    (fun i => (freeMapEquiv e x i).natAdd roots)
  invFun := Fin.addCases (fun i => i.castAdd free)
    (fun i => ((freeMapEquiv e x).symm i).natAdd roots)
  left_inv i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem vertex_vertexMapEquiv {n m roots free : Nat} (e : Fin n ≃ Fin m)
    (x : JointFlagSample n roots free) (i : Fin (roots + free)) :
    (x.map e).vertex (vertexMapEquiv e x i) = e (x.vertex i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [vertexMapEquiv]
  · simpa [vertexMapEquiv] using subsetVertex_freeMapEquiv e x j

def graphMapEquiv {n m roots free : Nat} {g : Graph (Fin n)} {h : Graph (Fin m)}
    (e : BooleanGraphEquiv g h) (x : JointFlagSample n roots free) :
    RootedGraphEquiv roots (x.graph g) ((x.map e.val).graph h) where
  graphEquiv := ⟨vertexMapEquiv e.val x, by
    intro i j
    change h.adj ((x.map e.val).vertex (vertexMapEquiv e.val x i))
      ((x.map e.val).vertex (vertexMapEquiv e.val x j)) = g.adj (x.vertex i) (x.vertex j)
    rw [vertex_vertexMapEquiv, vertex_vertexMapEquiv]
    exact e.property _ _⟩
  fixed i hi := by
    change vertexMapEquiv e.val x i = i
    have he : i = (i.castLT hi).castAdd free := (Fin.castAdd_castLT free i hi).symm
    have hleft : vertexMapEquiv e.val x ((i.castLT hi).castAdd free) =
        (i.castLT hi).castAdd free := by
      change Fin.addCases (motive := fun _ => Fin (roots + free))
        (fun j : Fin roots => j.castAdd free)
        (fun j => (freeMapEquiv e.val x j).natAdd roots)
        ((i.castLT hi).castAdd free) = (i.castLT hi).castAdd free
      exact Fin.addCases_left _
    exact (congrArg (vertexMapEquiv e.val x) he).trans (hleft.trans he.symm)

end JointFlagSample

end InducedPentagons.Paper



namespace InducedPentagons.Paper

theorem jointRootCheck_map {n m roots free : Nat} (typeMask : Nat)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (x : JointFlagSample n roots free) :
    jointRootCheck (free := free) typeMask h (x.map e.val).1 =
      jointRootCheck (free := free) typeMask g x.1 := by
  simp only [jointRootCheck, JointFlagSample.map_root, e.property]

theorem jointFlagPairHasTypes_map_iff {n m roots free dimension : Nat}
    (hn : n = roots + 2 * free) (hm : m = roots + 2 * free)
    (typeMask : Nat) (basis : Vector Nat dimension)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (i j : Fin dimension) (x : JointFlagSample n roots free) :
    JointFlagPairHasTypes hm typeMask basis h i j (x.map e.val) ↔
      JointFlagPairHasTypes hn typeMask basis g i j x := by
  have hl := JointFlagSample.graphMapEquiv e x
  have hr := JointFlagSample.graphMapEquiv e (x.swap hn)
  rw [JointFlagSample.map_swap hn hm] at hr
  simp only [JointFlagPairHasTypes, jointRootCheck_map typeMask e x]
  constructor
  · rintro ⟨hv, ⟨el⟩, ⟨er⟩⟩
    exact ⟨hv, ⟨hl.trans el⟩, ⟨hr.trans er⟩⟩
  · rintro ⟨hv, ⟨el⟩, ⟨er⟩⟩
    exact ⟨hv, ⟨hl.symm.trans el⟩, ⟨hr.symm.trans er⟩⟩

def jointFlagPairTypesEquiv {n m roots free dimension : Nat}
    (hn : n = roots + 2 * free) (hm : m = roots + 2 * free)
    (typeMask : Nat) (basis : Vector Nat dimension)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (i j : Fin dimension) :
    {x : JointFlagSample n roots free // JointFlagPairHasTypes hn typeMask basis g i j x} ≃
      {x : JointFlagSample m roots free // JointFlagPairHasTypes hm typeMask basis h i j x} :=
  (JointFlagSample.mapEquiv e.val).subtypeEquiv (fun x =>
    (jointFlagPairHasTypes_map_iff hn hm typeMask basis e i j x).symm)

theorem jointFlagPairTypesCount_isomorphic {n m roots free dimension : Nat}
    (hn : n = roots + 2 * free) (hm : m = roots + 2 * free)
    (typeMask : Nat) (basis : Vector Nat dimension)
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (i j : Fin dimension) :
    Nat.card {x : JointFlagSample n roots free // JointFlagPairHasTypes hn typeMask basis g i j x} =
      Nat.card {x : JointFlagSample m roots free // JointFlagPairHasTypes hm typeMask basis h i j x} :=
  Nat.card_congr (jointFlagPairTypesEquiv hn hm typeMask basis e i j)

theorem jointFlagPairCount_isomorphic {n m roots free dimension : Nat}
    (hn : n = roots + 2 * free) (hm : m = roots + 2 * free)
    (typeMask : Nat) (basis : Vector Nat dimension)
    (classify : Graph (Fin (roots + free)) → Fin dimension)
    (hclassify : ∀ g, rootTypeCheck roots typeMask g = true → ∀ i,
      classify g = i ↔ Nonempty (RootedGraphEquiv roots g
        (maskGraph (roots + free) basis[i])))
    {g : Graph (Fin n)} {h : Graph (Fin m)} (e : BooleanGraphEquiv g h)
    (i j : Fin dimension) :
    jointFlagPairCount hn (jointRootCheck (free := free) typeMask g)
      (fun x => classify (x.graph g)) i j =
    jointFlagPairCount hm (jointRootCheck (free := free) typeMask h)
      (fun x => classify (x.graph h)) i j := by
  rw [jointFlagPairCount_semantics hn typeMask basis classify hclassify,
    jointFlagPairCount_semantics hm typeMask basis classify hclassify]
  exact jointFlagPairTypesCount_isomorphic hn hm typeMask basis e i j

end InducedPentagons.Paper



