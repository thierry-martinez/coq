(* Disable warning 40: Constructor or label name used out of scope.
   (Type-directed constructor and label selection.) *)
[@@@ocaml.warning "-40"]

(** {5 Compilation of pattern-matching } *)

(** {6 Pattern-matching errors } *)
type pattern_matching_error =
  | BadPattern of Names.constructor * EConstr.constr
  | BadConstructor of Names.constructor * Names.inductive
  | WrongNumargConstructor of Names.constructor * int
  | WrongNumargInductive of Names.inductive * int
  | UnusedClause of Glob_term.cases_pattern list
  | NonExhaustive of Glob_term.cases_pattern list
  | CannotInferPredicate of (EConstr.constr * EConstr.types) array

exception PatternMatchingError of
  Environ.env * Evd.evar_map * pattern_matching_error

let raise_pattern_matching_error ?loc (env,sigma,te) =
  Loc.raise ?loc (PatternMatchingError(env,sigma,te))

let error_bad_constructor ?loc env cstr ind =
  raise_pattern_matching_error ?loc
    (env, Evd.empty, BadConstructor (cstr,ind))

let error_wrong_numarg_constructor ?loc env c n =
  raise_pattern_matching_error ?loc
    (env, Evd.empty, WrongNumargConstructor(c,n))

let error_wrong_numarg_inductive ?loc env c n =
  raise_pattern_matching_error ?loc (env, Evd.empty, WrongNumargInductive(c,n))

let rec irrefutable env (pat : Glob_term.cases_pattern) =
  match DAst.get pat with
  | PatVar name -> true
  | PatCstr (cstr,args,_) ->
      let ind = Names.inductive_of_constructor cstr in
      let (_,mip) = Inductive.lookup_mind_specif env ind in
      let one_constr = Int.equal (Array.length mip.mind_user_lc) 1 in
      one_constr && List.for_all (irrefutable env) args

type compile_cases_typing_fun =
    Evardefine.type_constraint -> GlobEnv.t -> Evd.evar_map ->
      Glob_term.glob_constr -> Evd.evar_map * EConstr.unsafe_judgment

module type TypeS = sig
  type t
end

module Eq = struct
   type ('a, 'b) t = ('a, 'b) Util.eq = Refl : ('a, 'a) t

   let sym : type a b . (a, b) t -> (b, a) t = Util.sym

   let trans : type a b c . (a, b) t -> (b, c) t -> (a, c) t =
   fun Refl Refl -> Refl

   let cast : type a b . (a, b) t -> a -> b = fun Refl -> Fun.id

   let option : type a b . (a, b) t -> (a option, b option) t = fun Refl -> Refl

   let list : type a b . (a, b) t -> (a list, b list) t = fun Refl -> Refl

   let array : type a b . (a, b) t -> (a array, b array) t = fun Refl -> Refl

   let pair : type a b c d. (a, b) t -> (c, d) t -> (a * c, b * d) t =
   fun Refl Refl -> Refl

   let ( ^* ) = pair

   let arrow : type a b c d. (a, b) t -> (c, d) t -> (a -> c, b -> d) t =
   fun Refl Refl -> Refl

   let ( ^-> ) = arrow

   let endo eq = arrow eq eq
end

module Phantom (Type : TypeS) : sig
  type 'a t

  val eq : ('a t, Type.t) Eq.t

  val transtype : ('a t, 'b t) Eq.t
end = struct
  type 'a t = Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

module Phantom2 (Type : TypeS) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, Type.t) Eq.t
end = struct
  type ('a, 'b) t = Type.t

  let eq = Eq.Refl
end

module Phantom3 (Type : TypeS) : sig
  type ('a, 'b, 'c) t

  val eq : (('a, 'b, 'c) t, Type.t) Eq.t
end = struct
  type ('a, 'b, 'c) t = Type.t

  let eq = Eq.Refl
end

module type UnaryTypeS = sig
  type 'a t
end

module PhantomPoly (Type : UnaryTypeS) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, 'a Type.t) Eq.t

  val transtype : (('a, 'b) t, ('a, 'c) t) Eq.t
end = struct
  type ('a, 'b) t = 'a Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

module Nat = struct
  (* Constructors Zero and Succ are never used:
     they are here for injectivity. *)

  type zero = Zero [@@ocaml.warning "-37"]

  type 'a succ = Succ [@@ocaml.warning "-37"]

  type 'a t =
    | O : zero t
    | S : 'a t -> 'a succ t

  let rec to_int : type a . ?add:int -> a t -> int  = fun ?(add = 0) a ->
    match a with
    | O -> add
    | S a -> to_int ~add:(add + 1) a

  type exists = Exists : 'a t -> exists

  let of_int ?accu n =
    let rec aux : type a . a t -> int -> exists = fun accu n ->
      if n > 0 then
        aux (S accu) (pred n)
      else if n = 0 then
        Exists accu
      else
        assert false in
    match accu with
    | None -> aux O n
    | Some accu -> aux accu n

  type ('a, 'b, 'a_plus_b) plus =
    | Zero_l : (zero, 'a, 'a) plus
    | Succ_plus : ('a, 'b, 'c) plus -> ('a succ, 'b, 'c succ) plus

  type ('a, 'b) add =
    Exists : 'a_plus_b t * ('a, 'b, 'a_plus_b) plus -> ('a, 'b) add

  let rec add : type a b . a t -> b t -> (a, b) add = fun a b ->
    match a with
    | O -> Exists (b, Zero_l)
    | S a ->
        let Exists (c, a_plus_b) = add a b in
        Exists (S c, Succ_plus a_plus_b)

  let rec plus_succ : type a b a_plus_b .
        (a, b, a_plus_b) plus -> (a, b succ, a_plus_b succ) plus = fun plus ->
    match plus with
    | Zero_l -> Zero_l
    | Succ_plus plus -> Succ_plus (plus_succ plus)

  let rec zero_r : type a . a t -> (a, zero, a) plus = fun a ->
    match a with
    | O -> Zero_l
    | S a -> Succ_plus (zero_r a)

  let rec plus_commut : type a b sum .
        b t -> (a, b, sum) plus -> (b, a, sum) plus = fun b plus ->
    match plus with
    | Zero_l -> zero_r b
    | Succ_plus plus -> plus_succ (plus_commut b plus)
end

module Vector = struct
  type ('a, 'length) t =
    | [] : ('a, Nat.zero) t
    | (::) : 'a * ('a, 'length) t -> ('a, 'length Nat.succ) t

  type 'a exists = Exists : ('a, 'length) t -> 'a exists

  let rec of_list : type a . a list -> a exists = fun l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_list tl in
        Exists (hd :: tl)

  let rec length : type a length . (a, length) t -> length Nat.t = fun l ->
    match l with
    | [] -> O
    | _hd :: tl -> S (length tl)

  let rec of_list_of_length : type a length . a list -> length Nat.t ->
    (a, length) t = fun l len ->
    match l, len with
    | [], Nat.O -> []
    | hd :: tl, Nat.S len -> hd :: of_list_of_length tl len
    | _ -> assert false

  let rec find : type length . ('a -> bool) -> ('a, length) t -> 'a = fun p l ->
    match l with
    | [] -> raise Not_found
    | hd :: tl ->
        if p hd then hd
        else find p tl

  let rec map : type length . ('a -> 'b) -> ('a, length) t -> ('b, length) t =
  fun f l ->
    match l with
    | [] -> []
    | hd :: tl -> f hd :: map f tl

  let rec map2 : type length .
    ('a -> 'b -> 'c) -> ('a, length) t -> ('b, length) t -> ('c, length) t =
  fun f l1 l2 ->
    match l1, l2 with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 -> f hd1 hd2 :: map2 f tl1 tl2

  let rec map_rev_append : type l l0 l1 .
        ('a -> 'b) -> ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus ->
        ('b, l) t = fun f l0 l1 plus ->
    match l0, plus with
    | [], Zero_l -> l1
    | hd :: tl, Succ_plus plus ->
        map_rev_append f tl (f hd :: l1) (Nat.plus_succ plus)
end

module type Monad = sig
   type 'a t

   module Ops : sig
     val return : 'a -> 'a t

     val (let*) : 'a t -> ('a -> 'b t) -> 'b t
   end
end

module MonadUtils (M : Monad) = struct
  let rec list_map : type a b .
        (a -> b M.t) -> a list -> b list M.t =
    fun f l ->
      let open M.Ops in
      match l with
      | [] -> return []
      | h :: t ->
          let* h' = f h in
          let* t' = list_map f t in
          return (h' :: t')

  let rec vector_map : type length a b .
        (a -> b M.t) -> (a, length) Vector.t -> (b, length) Vector.t M.t =
    fun f v ->
      let open M.Ops in
      let open Vector in
      match v with
      | [] -> return []
      | h :: t ->
          let* h' = f h in
          let* t' = vector_map f t in
          return (h' :: t')

  let option_map : type state a b .
        (a -> b M.t) -> a option -> b option M.t =
    fun f o ->
      let open M.Ops in
      match o with
      | None -> return None
      | Some x ->
          let* x' = f x in
          return (Some x')
end

module OptionMonad = struct
  module Self = struct
    type 'a t = 'a option

    module Ops = struct
      let return x = Some x

      let (let*) = Option.bind
    end
  end

  include Self

  include MonadUtils (Self)
end

module type Type = sig
  type t
end

module StateMonad (State : Type) = struct
  module Self = struct
    type 'a t = State.t -> State.t * 'a

    module Ops = struct
     let return x sigma =
       (sigma, x)

     let (let*) x f sigma =
       let (sigma, y) = x sigma in
       f y sigma
    end
  end

  include Self

  let get : State.t t =
    fun state -> (state, state)

  let eq : type a b . (a, b) Eq.t -> (a t, b t) Eq.t =
    fun Refl -> Refl


  let array_init : type a . int -> (int -> a t) -> a array t =
  fun len f state ->
     let state_ref = ref state in
     let result =
       Array.init len (fun i ->
         let state, result = f i !state_ref in
         state_ref := state;
         result) in
     !state_ref, result

  include MonadUtils (Self)
end

module Env = struct
  include Phantom (struct type t = Environ.env end)

  let pair :
    type a b c d . (a t, b t) Eq.t -> (c t, d t) Eq.t ->
      ((a * c) t, (b * d) t) Eq.t = fun _ _ -> transtype

  let zero_l : type env . ((Nat.zero * env) t, env t) Eq.t = transtype

  let zero_r : type env . ((env * Nat.zero) t, env t) Eq.t = transtype

  let assoc : type a b c . (((a * b) * c) t, (a * (b * c)) t) Eq.t = transtype

  let commut : type a b . ((a * b) t, (b * a) t) Eq.t = transtype
end

module Height = struct
  include Phantom (struct type t = int end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) : (a t, b t) Eq.t =
    transtype

  let zero : Nat.zero t = Eq.cast (Eq.sym eq) 0

  let one : (Nat.zero Nat.succ) t = Eq.cast (Eq.sym eq) 1

  let add (type a b) (a : a t) (b : b t) : (a * b) t =
    Eq.cast (Eq.sym eq) (Eq.cast eq a + Eq.cast eq b)

  type 'n to_nat = Exists : 'm Nat.t * ('m Env.t, 'n Env.t) Eq.t -> 'n to_nat

  let to_nat : type n . n t -> n to_nat = fun n ->
    let n = Eq.cast eq n in
    let Exists m = Nat.of_int n in
    Exists (m, Env.transtype)

  let to_int n =
    Eq.cast eq n
end

module InductiveDef = struct
  include Phantom (struct type t = Names.inductive end)

  let equal (type ind ind') (ind : ind t) (ind' : ind' t) :
      (ind t, ind' t) Eq.t option =
    if Names.eq_ind (Eq.cast eq ind) (Eq.cast eq ind') then
      Some transtype
    else
      None
end

module type AbstractTermS = sig
  type t

  val liftn : int -> int -> t -> t

  val mkProp : t

  val mkInd : Names.inductive -> t

  val mkApp : t * t array -> t
end

module AbstractTerm (X : AbstractTermS) = struct
  include Phantom (struct type t = X.t end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype

  let liftn (type env n m)
      (n : n Height.t) (m : m Height.t) (term : (env * m) t) :
      ((env * n) * m) t =
    Eq.cast (Eq.sym eq)
      (X.liftn (Eq.cast Height.eq n) (succ (Eq.cast Height.eq m))
         (Eq.cast eq term))

  let lift (type env n m) (n : n Height.t) (term : env t) : (env * n) t =
    Eq.cast (Eq.arrow (morphism Env.zero_r) (morphism Env.zero_r))
      (liftn n Height.zero) term

  let mkProp () : 'env t = Eq.cast (Eq.sym eq) X.mkProp

  let mkInd (ind : 'ind InductiveDef.t) : 'env t =
    Eq.cast (Eq.sym (Eq.arrow InductiveDef.eq eq)) X.mkInd ind

  let mkApp (f : 'env t) (args : 'env t array) : 'env t =
    Eq.cast (Eq.sym eq) (X.mkApp (Eq.cast eq f, Eq.cast (Eq.array eq) args))
end

module Term = struct
  include AbstractTerm (Constr)
end

module ETerm = struct
  include AbstractTerm (struct
    include EConstr

    let liftn = Vars.liftn
  end)

  let whd_all (type env) (env : env Env.t) (sigma : Evd.evar_map)
      (term : env t) =
    Eq.cast (Eq.sym eq)
      (Reductionops.whd_all (Eq.cast Env.eq env) sigma
         (Eq.cast eq term))

  module Substl = struct
    type 'a term = 'a t

    type ('env, 'length) t =
      | [] : ('env * Nat.zero, Nat.zero) t
      | (::) :
          ('env * 'length) term * ('env * 'length, 'length) t ->
            ('env * 'length Nat.succ, 'length Nat.succ) t

    let rec to_list :
    type env length . (env, length) t -> EConstr.constr list = function
      | [] -> []
      | hd :: tl -> Eq.cast eq hd :: to_list tl

    let rec fake :
    type env length . length Nat.t -> (env * length, length) t = function
      | O -> []
      | S n -> mkProp () :: fake n
  end

  let substnl (type env n length) (substl : (env * length, length) Substl.t)
      (n : n Height.t) (t : ((env * length) * n) t) : (env * n) t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq))
      (EConstr.Vars.substnl (Substl.to_list substl) (Eq.cast Height.eq n)) t

  let substl (type env length) (substl : (env * length, length) Substl.t)
      (t : (env * length) t) : env t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq))
      (EConstr.Vars.substl (Substl.to_list substl)) t

  let subst1 (type env) (s : env t) (t : (env * Nat.zero Nat.succ) t) : env t =
    substl [Eq.cast (morphism (Eq.sym Env.zero_r)) s] t

  let noccur_between (sigma : Evd.evar_map) n m (term : 'env t) : bool =
    EConstr.Vars.noccur_between sigma n m (Eq.cast eq term)
end

module EvarMapMonad = struct
  include StateMonad (struct type t = Evd.evar_map end)

  let new_type_evar (env : 'env Env.t) rigid : ('env ETerm.t * Sorts.t) t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.pair (Eq.sym ETerm.eq) Refl))
      (Evarutil.new_type_evar (Eq.cast Env.eq env) sigma rigid)

  let new_evar (env : 'env Env.t) (ty : 'env ETerm.t) : 'env ETerm.t t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.sym ETerm.eq))
      (Evarutil.new_evar (Eq.cast Env.eq env) sigma (Eq.cast ETerm.eq ty))
end

module Judgment = struct
  include Phantom (struct type t = EConstr.unsafe_judgment end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      a t -> b t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq)) Fun.id

  let uj_val (j : 'env t) : 'env ETerm.t =
    Eq.cast (Eq.sym (Eq.arrow eq ETerm.eq)) (fun j -> j.uj_val) j

  let uj_type (j : 'env t) : 'env ETerm.t =
    Eq.cast (Eq.sym (Eq.arrow eq ETerm.eq)) (fun j -> j.uj_type) j

  let inh_conv_coerce_to (type env) ~program_mode ~resolve_tc (env : env Env.t)
      (judgment : env t) (t : env ETerm.t) :
      (env t  * Coercion.coercion_trace option) EvarMapMonad.t =
    Eq.cast (EvarMapMonad.eq (Eq.pair (Eq.sym eq) Refl)) (fun sigma ->
      let sigma, result, trace =
        Coercion.inh_conv_coerce_to ~program_mode resolve_tc
          (Eq.cast Env.eq env)
          sigma (Eq.cast eq judgment) (Eq.cast ETerm.eq t) in
       (sigma, (result, trace)))

  let map (type a b) (f : a ETerm.t -> b ETerm.t) (j : a t) : b t =
    match Eq.cast eq j with
    | { uj_val; uj_type } ->
        Eq.cast (Eq.sym eq) {
          uj_val = Eq.cast (Eq.arrow ETerm.eq ETerm.eq) f uj_val;
          uj_type = Eq.cast (Eq.arrow ETerm.eq ETerm.eq) f uj_type; }
end

module Declaration = struct
  include Phantom (struct
    type t = (EConstr.constr, EConstr.constr) Context.Rel.Declaration.pt
  end)

  let assum (type env) as_name (ty : env ETerm.t) : env t =
    Eq.cast (Eq.sym eq) (LocalAssum (as_name, Eq.cast ETerm.eq ty))

  let local_def (type env) (as_name : Names.Name.t Context.binder_annot)
      (judgment : env Judgment.t) : env t =
    let uj_val = Eq.cast ETerm.eq (Judgment.uj_val judgment) in
    let uj_type = Eq.cast ETerm.eq (Judgment.uj_type judgment) in
    Eq.cast (Eq.sym eq) (LocalDef (as_name, uj_val, uj_type))
end

module RelContext = struct
  include Phantom2 (struct
    type t = (EConstr.constr, EConstr.constr) Context.Rel.pt
  end)

  let morphism (type a b c d) (_ : (a Env.t, b Env.t) Eq.t)
      (_ : (c Env.t, d Env.t) Eq.t) : (a, c) t -> (b, d) t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq)) Fun.id

  let empty () : ('env, Nat.zero) t =
    Eq.cast (Eq.sym eq) Context.Rel.empty

  let add (type env length) (declaration : (env * length) Declaration.t)
      (context : (env, length) t) : (env, length Nat.succ) t =
    Eq.cast (Eq.sym eq)
      (Context.Rel.add (Eq.cast Declaration.eq declaration)
         (Eq.cast eq context))

  let push (type outer) (type length_inner) (type length_outer)
      (inner_context : (outer * length_outer, length_inner) t)
      (outer_context : (outer, length_outer) t) :
      (outer, length_inner * length_outer) t =
    Eq.cast (Eq.sym eq)
      (Context.Rel.fold_outside Context.Rel.add
         ~init:(Eq.cast eq outer_context) (Eq.cast eq inner_context))

  let length_morphism (type env a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (env, a) t -> (env, b) t =
    Eq.cast (Eq.arrow (Eq.sym eq) (Eq.sym eq)) Fun.id

  let untyped_liftn n m context =
    let add decl (new_context, m) =
      new_context |> Context.Rel.add
        (Context.Rel.Declaration.map_constr (EConstr.Vars.liftn n m) decl),
      succ m in
    let new_context, _m =
      Context.Rel.fold_outside add context ~init:(Context.Rel.empty, m) in
    new_context

  let liftn (type env n m length)
      (n : n Height.t) (m : m Height.t) (context : (env * m, length) t) :
      ((env * n) * m, length) t =
    Eq.cast (Eq.sym eq)
      (untyped_liftn (Eq.cast Height.eq n) (succ (Eq.cast Height.eq m))
         (Eq.cast eq context))

  let lift (type env n m length) (n : n Height.t) (context : (env, length) t) :
      (env * n, length) t =
    morphism Env.zero_r Eq.Refl
      (liftn n Height.zero (morphism (Eq.sym Env.zero_r) Eq.Refl context))

  let length (type env length) (context : (env, length) t) : length Height.t =
    Eq.cast (Eq.sym (Eq.arrow eq Height.eq)) Context.Rel.length context

  type 'env exists = Exists : ('env, 'length) t -> 'env exists
end

module GlobalEnv = struct
  include Phantom (struct type t = GlobEnv.t end)

  let env glob_env =
    Eq.cast (Eq.sym Env.eq) (GlobEnv.env (Eq.cast eq glob_env))

  let push_rel (type env) ~hypnaming
      (sigma : Evd.evar_map) (d : env Declaration.t)
      (glob_env : env t) : env Declaration.t * (env * Nat.zero Nat.succ) t =
    Eq.cast (Eq.pair (Eq.sym Declaration.eq) (Eq.sym eq))
      (GlobEnv.push_rel ~hypnaming sigma (Eq.cast Declaration.eq d)
         (Eq.cast eq glob_env))

  let push_rel_context (type env) (type height) ~hypnaming
      (sigma : Evd.evar_map) (context : (env, height) RelContext.t)
      (glob_env : env t) : (env, height) RelContext.t * (env * height) t =
    Eq.cast (Eq.sym (Eq.arrow eq (Eq.pair RelContext.eq eq)))
      (GlobEnv.push_rel_context ~hypnaming sigma
         (Eq.cast RelContext.eq context)) glob_env

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype
end

module Index = struct
  include Phantom (struct type t = int end)
end

module Tuple = struct
  include PhantomPoly (struct type 'a t = 'a array end)

  module Ops = struct
    let (.%()) (type length) (tuple : ('a, length) t) (index : length Index.t) =
      Array.unsafe_get (Eq.cast eq tuple) (Eq.cast Index.eq index)

    let (.%()<-) (type length) (tuple : ('a, length) t)
        (index : length Index.t) (value : 'a) =
      Array.unsafe_set (Eq.cast eq tuple) (Eq.cast Index.eq index) value
  end

  let length (type length) (t : ('a, length) t) : length Height.t =
    Eq.cast (Eq.sym (Eq.arrow eq Height.eq)) Array.length t

  let make (l : 'length Height.t) (default : 'a) : ('a, 'length) t =
    Eq.cast Eq.(sym (Height.eq ^-> Refl ^-> eq)) Array.make l default

  let iter (t : ('a, 'length) t) (f : 'length Index.t -> unit) : unit =
    for i = 0 to Array.length (Eq.cast eq t) - 1 do
      f (Eq.cast (Eq.sym Index.eq) i)
    done

  type 'a exists = Exists : ('a, 'length) t -> 'a exists
end

module InductiveSpecif = struct
  include Phantom2 (struct type t = Inductive.mind_specif end)

  let lookup (type env ind) (env : env Env.t) (ind : ind InductiveDef.t) :
      (env, ind) t =
    Eq.cast (Eq.sym (Eq.arrow Env.eq (Eq.arrow InductiveDef.eq eq)))
      Inductive.lookup_mind_specif env ind

  let constructors (type env ind) (specif : (env, ind) t) :
      (env Term.t) Tuple.exists =
    Exists (Eq.cast (Eq.trans (Eq.array (Eq.sym (Term.eq))) (Eq.sym Tuple.eq))
      (snd (Eq.cast eq specif)).mind_user_lc)
end

module type AnnotatedS = sig
  type 'annot t
end

module AnnotatedVector (S : AnnotatedS) = struct
  type 'annot t =
    | [] : unit t
    | (::) : 'head S.t * 'tail t -> ('head * 'tail) t
end

module Constructor = struct
  include Phantom2 (struct type t = Names.constructor end)

  type exists = Exists : ('ind, 'arity) t -> exists

  let of_constructor (cstr : Names.constructor) : exists =
    Exists (Eq.cast (Eq.sym eq) cstr)

  let inductive (cstr : ('ind, 'arity) t) : 'ind InductiveDef.t =
    Eq.cast (Eq.sym (Eq.arrow eq InductiveDef.eq))
      Names.inductive_of_constructor cstr

  let index (cstr : ('ind, 'arity) t) : 'ind Index.t =
    Eq.cast (Eq.sym (Eq.arrow eq Index.eq))
      Names.index_of_constructor cstr

  let error_bad ?loc env cstr ind =
    raise_pattern_matching_error ?loc
      (Eq.cast Env.eq env, Evd.empty,
        BadConstructor (Eq.cast eq cstr, Eq.cast InductiveDef.eq ind))

  let error_wrong_numarg ?loc env c n =
    raise_pattern_matching_error ?loc
      (Eq.cast Env.eq env, Evd.empty, WrongNumargConstructor(Eq.cast eq c, n))
end

module InductiveFamily = struct
  include Phantom3 (struct type t = Inductiveops.inductive_family end)

  let get_arity (type env ind arity) (env : env Env.t)
      (indf : (env, ind, arity) t) : (env, arity) RelContext.t =
    Eq.cast (Eq.sym RelContext.eq) (List.map EConstr.of_rel_decl
      (fst (Inductiveops.get_arity (Eq.cast Env.eq env) (Eq.cast eq indf))))

  let build_dependent_inductive  (type env ind arity) (env : env Env.t)
      (indf : (env, ind, arity) t) : (env * arity) ETerm.t =
    Eq.cast (Eq.sym ETerm.eq)
      (EConstr.of_constr (Inductiveops.build_dependent_inductive
         (Eq.cast Env.eq env) (Eq.cast eq indf)))

  type ('env, 'ind) exists =
      Exists : ('env, 'ind, 'arity) t -> ('env, 'ind) exists

  let destruct (type env ind arity) (indf : (env, ind, arity) t) :
      ind InductiveDef.t Univ.puniverses * env Term.t list =
    let (ind, univ), params = Inductiveops.dest_ind_family (Eq.cast eq indf) in
    (Eq.cast (Eq.sym InductiveDef.eq) ind, univ),
    Eq.cast (Eq.list (Eq.sym Term.eq)) params

  let construct (type env ind arity)
      (ind : ind InductiveDef.t Univ.puniverses) (params : env Term.t list) :
      (env, ind, arity) t =
    Eq.cast (Eq.sym (Eq.arrow
      (Eq.pair (Eq.pair InductiveDef.eq Refl) (Eq.list Term.eq)) eq))
    Inductiveops.make_ind_family (ind, params)

  let to_inductive (type env ind arity) (indf : (env, ind, arity) t) :
      ind InductiveDef.t =
    let (ind, _univ), _params =
      Inductiveops.dest_ind_family (Eq.cast eq indf) in
    Eq.cast (Eq.sym InductiveDef.eq) ind

  let map (type ind arity a b) (f : a Term.t -> b Term.t)
      (indf : (a, ind, arity) t) : (b, ind, arity) t =
    let ind, params = destruct indf in
    construct ind (List.map f params)
end

module ConstructorSummary = struct
  include Phantom3 (struct type t = Inductiveops.constructor_summary end)

  let get (env : 'env Env.t) (indf : ('env, 'ind, 'arityf) InductiveFamily.t)
      (specif : ('env, 'ind) InductiveSpecif.t)
      (cstr : ('ind, 'arity) Constructor.t) : ('env, 'ind, 'arity) t =
    let indu, params =
      Eq.cast Eq.((InductiveDef.eq ^* Refl) ^* list Term.eq)
        (InductiveFamily.destruct indf) in
    let mib, mip = Eq.cast InductiveSpecif.eq specif in
    Eq.cast Eq.(sym (Refl ^-> Index.eq ^-> eq))
      Inductiveops.get_constructor (indu, mib, mip, params)
        (Constructor.index cstr)
end

module InductiveType = struct
  include Phantom2 (struct type t = Inductiveops.inductive_type end)

  type 'env exists = Exists : ('env, 'ind) t -> 'env exists

  let of_term_opt (type env) (env : env Env.t) (sigma : Evd.evar_map)
      (term : env ETerm.t) : env exists option =
    match
       Inductiveops.find_rectype (Eq.cast Env.eq env) sigma
        (Eq.cast ETerm.eq term)
    with
    | exception Not_found -> None
    | ind -> Some (Exists (Eq.cast (Eq.sym eq) ind))

  let destruct (type env ind) (ind_type : (env, ind) t) :
      (env, ind) InductiveFamily.exists * env ETerm.t list =
    let indf, real_args = Inductiveops.dest_ind_type (Eq.cast eq ind_type) in
    Exists (Eq.cast (Eq.sym InductiveFamily.eq) indf),
    Eq.cast (Eq.list (Eq.sym ETerm.eq)) real_args

  let construct (type env ind arity)
      (indf : (env, ind, arity) InductiveFamily.t)
      (real_args : env ETerm.t list) : (env, ind) t =
    Eq.cast (Eq.sym eq)
      (Inductiveops.make_ind_type
        (Eq.cast InductiveFamily.eq indf, Eq.cast (Eq.list ETerm.eq) real_args))

  let to_inductive_family (type env ind) (ind_type : (env, ind) t) :
      (env, ind) InductiveFamily.exists =
    let indf, _real_args = Inductiveops.dest_ind_type (Eq.cast eq ind_type) in
    Exists (Eq.cast (Eq.sym InductiveFamily.eq) indf)

  let to_real_args (type env ind) (ind_type : (env, ind) t) : env ETerm.t list =
    let _indf, real_args = Inductiveops.dest_ind_type (Eq.cast eq ind_type) in
    Eq.cast (Eq.list (Eq.sym ETerm.eq)) real_args

  let map (type ind a b) (f : a Term.t -> b Term.t)
      (ef : a ETerm.t -> b ETerm.t) (ind_type : (a, ind) t) :
      (b, ind) t =
    let Exists indf, real_args = destruct ind_type in
    construct (InductiveFamily.map f indf) (List.map ef real_args)

  let make_with_evars (type env ind) (env : env Env.t)
      (ind : ind InductiveDef.t) : (env, ind) t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let nb_args =
      Inductiveops.inductive_nallargs (Eq.cast Env.eq env)
        (Eq.cast InductiveDef.eq ind) in
    let* args = EvarMapMonad.array_init nb_args (fun _ ->
      let* (e, _) = EvarMapMonad.new_type_evar env Evd.univ_flexible_alg in
      EvarMapMonad.new_evar env e) in
    let* sigma = EvarMapMonad.get in
    return (Eq.cast (Eq.sym eq)
      (Inductiveops.find_rectype (Eq.cast Env.eq env) sigma
        (Eq.cast ETerm.eq (ETerm.mkApp (ETerm.mkInd ind) args))))
end

module AnnotLength = struct
  type ('ind, 'length) t =
    | O : (unit, Nat.zero) t
    | S : ('ind, 'length) t -> (_ * 'ind, 'length Nat.succ) t
end

module type MeasurableS = sig
  type ('env, 'annot, 'height) t

  val height : ('env, 'annot, 'height) t -> 'height Height.t
end

module MeasurableVector (S : MeasurableS) = struct
  type ('env, 'annot, 'height) t =
    | [] : ('env, unit, Nat.zero) t
    | (::) :
        ('env, 'annot_head, 'height_head) S.t *
        ('env, 'annot_tail, 'height_tail) t ->
          ('env, 'annot_head * 'annot_tail, 'height_head * 'height_tail) t

  let rec height : type env annot height .
        (env, annot, height) t -> height Height.t = fun v ->
    match v with
    | [] -> Height.zero
    | hd :: tl -> Height.add (S.height hd) (height tl)
end

module MeasurableVectorMap (S0 : MeasurableS) (S1 : MeasurableS) = struct
  module V0 = MeasurableVector (S0)

  module V1 = MeasurableVector (S1)

  type ('a, 'b) map =
      { f : 'annot 'height .
          ('a, 'annot, 'height) S0.t -> ('b, 'annot, 'height) S1.t }

  let rec map : type a b annot height .
        (a, b) map -> (a, annot, height) V0.t -> (b, annot, height) V1.t =
  fun f v ->
    match v with
    | [] -> []
    | hd :: tl -> f.f hd :: map f tl
end

module CasesPattern = struct
  type unknown = U

  type 'ind known = K

  type 'ind desc =
    | Var
    | Cstr : {
      cstr : ('ind, 'arity) Constructor.t;
      args : (Glob_term.cases_pattern, 'arity) Vector.t;
    } -> 'ind desc

  type 'ind content = {
      name : Names.Name.t;
      desc : 'ind desc;
    }

  type 'ind t = 'ind content CAst.t

  let get_var (type ind) (pat : ind t) : Names.Name.t option =
    match pat.v.desc with
    | Var -> Some pat.v.name
    | _ -> None

  let get_name (type ind) (pat : ind t) : Names.Name.t =
    pat.v.name

  let of_var (type ind) (name : (Names.Name.t, [`any]) DAst.t) : ind t =
    Eq.cast (Eq.sym eq) (DAst.map (fun name -> Glob_term.PatVar name) name)

  type 'item inferred =
    | Unknown : unknown inferred
    | Known : 'ind InductiveDef.t -> 'ind known inferred

  let coerce_to ?loc (env : 'env Env.t) (pat : 'ind known t)
      ~(pat_ind : 'ind InductiveDef.t) ~(tgt_ind : 'ind' InductiveDef.t) :
      'ind' known t =
    Eq.cast (Eq.sym (Eq.arrow (Env.eq) (Eq.arrow eq (Eq.arrow InductiveDef.eq
      (Eq.arrow InductiveDef.eq eq)))))
      (Coercion.inh_pattern_coerce_to ?loc) env pat pat_ind tgt_ind
end

module CasesPatterns = AnnotatedVector (CasesPattern)

module Tomatch = struct
  type ('env, 'ind, 'height) inductive_type =
    | None : ('env, CasesPattern.unknown, Nat.zero) inductive_type
    | Some :
        ('env, 'ind) InductiveType.t ->
          ('env, 'ind CasesPattern.known, 'height) inductive_type

  type ('env, 'ind, 'height) t = {
      judgment : 'env Judgment.t;
      inductive_type : ('env, 'ind, 'height) inductive_type;
      return_pred_height : 'height Height.t;
    }

  let height t = t.return_pred_height

  let map (type a b ind length)
      (f : a Term.t -> b Term.t) (ef : a ETerm.t -> b ETerm.t)
      (tomatch : (a, ind, length) t) : (b, ind, length) t =
    { judgment = Judgment.map ef tomatch.judgment;
      inductive_type =
        begin match tomatch.inductive_type with
        | None -> None
        | Some ind -> Some (InductiveType.map f ef ind)
        end;
      return_pred_height = tomatch.return_pred_height; }
end

module TomatchVector = struct
  include MeasurableVector (Tomatch)

  include MeasurableVectorMap (Tomatch) (Tomatch)
end

module PrepareTomatch (EqnLength : Type) = struct
  module TomatchWithContext = struct
    type ('env, 'ind, 'height) t = {
        tomatch : ('env, 'ind, 'height) Tomatch.t;
        return_pred_context : ('env, 'height) RelContext.t;
        pats : ('ind CasesPattern.t, EqnLength.t) Vector.t;
      }

    type 'env exists =
        Exists : ('env, 'ind, 'height) t -> 'env exists

    let height t = Tomatch.height t.tomatch

    type ('env, 'item) inferred =
      | Unknown : ('env, CasesPattern.unknown) inferred
      | Known :
          ('env, 'ind) InductiveType.t ->
            ('env, 'ind CasesPattern.known) inferred

    type 'env infer_type =
        Inferred :
          ('env, 'ind) inferred *
          ('ind CasesPattern.t, EqnLength.t) Vector.t ->
            'env infer_type

    let rec check : type env ind pat_length accu_length .
          env Env.t ->
          (pat_length, accu_length, EqnLength.t) Nat.plus ->
          (env, ind) InductiveType.t ->
          (Glob_term.cases_pattern, pat_length) Vector.t ->
          (ind CasesPattern.known CasesPattern.t, accu_length) Vector.t ->
          env infer_type = fun env plus ind_type pats accu ->
      match pats, plus with
      | [], Zero_l ->
          Inferred (
            Known ind_type, Vector.map_rev_append Fun.id accu []
              (Nat.plus_commut (Vector.length accu) plus))
      | hd :: tl, Succ_plus plus ->
          match DAst.get hd with
          | PatVar name ->
              check env (Nat.plus_succ plus) ind_type tl
                (Eq.cast (Eq.sym CasesPattern.eq) hd :: accu)
          | PatCstr (cstr, args, alias) ->
              let Exists indf = InductiveType.to_inductive_family ind_type in
              let ind = InductiveFamily.to_inductive indf in
              let Exists cstr = Constructor.of_constructor cstr in
              let ind' = Constructor.to_inductive cstr in
              let pat =
                match InductiveDef.equal ind ind' with
                | Some Refl ->
                    Eq.cast (Eq.sym CasesPattern.eq) hd
                | None ->
                    let loc = hd.CAst.loc in
                    try
                      CasesPattern.coerce_to ?loc env
                        (Eq.cast (Eq.sym CasesPattern.eq) hd) ~pat_ind:ind'
                        ~tgt_ind:ind
                    with Not_found ->
                      Constructor.error_bad ?loc:hd.CAst.loc env cstr ind in
              check env (Nat.plus_succ plus) ind_type tl (pat :: accu)

    let rec infer : type pat_length var_length .
          'env Env.t ->
          (pat_length, var_length, EqnLength.t) Nat.plus ->
          (Glob_term.cases_pattern, pat_length) Vector.t ->
          ((Names.Name.t, [`any]) DAst.t, var_length) Vector.t ->
          'env infer_type EvarMapMonad.t =
    fun env plus pats vars ->
      let open EvarMapMonad.Ops in
      match pats, plus with
      | [], Zero_l ->
          return (Inferred (
            Unknown,
            Vector.map_rev_append CasesPattern.of_var vars []
              (Nat.plus_commut (Vector.length vars) plus)))
      | hd :: tl, Succ_plus plus  ->
          match DAst.get hd with
          | PatVar name ->
              infer env (Nat.plus_succ plus) tl
                (DAst.map (fun _ -> name) hd :: vars)
          | PatCstr (cstr, args, alias) ->
              let Exists cstr = Constructor.of_constructor cstr in
              let ind = Constructor.to_inductive cstr in
              let vars_pat =
                Vector.map_rev_append CasesPattern.of_var vars []
                  (Nat.zero_r (Vector.length vars)) in
              let* ind_type = InductiveType.make_with_evars env ind in
              return (check env (Nat.plus_succ plus) ind_type tl
                (Eq.cast (Eq.sym CasesPattern.eq) hd :: vars_pat))

    let infer_type  (type env) (env : env Env.t)
        (sigma : Evd.evar_map) (judgment : env Judgment.t)
        (pats : (Glob_term.cases_pattern, EqnLength.t) Vector.t) :
        env infer_type EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      match
        InductiveType.of_term_opt env sigma
          (ETerm.whd_all env sigma (Judgment.uj_type judgment))
      with
      | None ->
          infer env (Nat.zero_r (Vector.length pats)) pats []
      | Some (Exists ind_type) ->
          return (check env (Nat.zero_r (Vector.length pats)) ind_type pats [])

    let make (type env) (env : env Env.t) (sigma : Evd.evar_map)
        (judgment : env Judgment.t)
        (predicate_pattern : Glob_term.predicate_pattern)
        (pats : (Glob_term.cases_pattern, EqnLength.t) Vector.t) :
        env exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* Inferred (inferred, pats) = infer_type env sigma judgment pats in
      match inferred with
      | Unknown ->
          return (Exists {
            tomatch = {
              judgment;
              inductive_type = None;
              return_pred_height = Height.zero;
            };
            return_pred_context = RelContext.empty ();
            pats;
          })
      | Known inductive_type ->
          let Exists indf = InductiveType.to_inductive_family inductive_type in
          let arity = InductiveFamily.get_arity env indf in
          let as_name, in_names = predicate_pattern in
          let ty = InductiveFamily.build_dependent_inductive env indf in
          let return_pred_context =
            RelContext.add (Declaration.assum
              (Context.make_annot as_name Relevant) ty) arity in
          let return_pred_height =
            RelContext.length return_pred_context in
          return (Exists {
            tomatch = {
              judgment;
              inductive_type = Some inductive_type;
              return_pred_height;
            };
            return_pred_context;
            pats;
          })
  end

  module TomatchWithContextVector = struct
    include MeasurableVector (TomatchWithContext)

    let to_tomatch_vector v =
      let module Map =
        MeasurableVectorMap (TomatchWithContext)
          (Tomatch) in
      Map.map { f = fun tomatch -> tomatch.tomatch } v

    let rec make_return_pred_context :
    type env annot return_pred_height .
          env Env.t -> Evd.evar_map ->
            (env, annot, return_pred_height) t ->
            (env, return_pred_height) RelContext.t *
                return_pred_height Height.t =
    fun env sigma tomatchl ->
      match tomatchl with
      | [] -> RelContext.empty (), Height.zero
      | { return_pred_context;
          tomatch = { return_pred_height; _ }} :: tl ->
          let tl, length = make_return_pred_context env sigma tl in
          RelContext.push (RelContext.lift length return_pred_context) tl,
          Height.add return_pred_height length
      | _ -> .

    type ('env, 'length) exists =
        Exists :
          ('env, 'ind, 'return_pred_height) t * ('ind, 'length) AnnotLength.t ->
          ('env, 'length) exists

    let rec of_vector : type env tomatch_length .
          (env TomatchWithContext.exists, tomatch_length) Vector.t ->
            (env, tomatch_length) exists = fun l ->
      match l with
      | [] -> Exists ([], O)
      | Exists hd :: tl ->
          let Exists (tl, len) = of_vector tl in
          Exists (hd :: tl, S len)
  end
end

module Rhs = struct
  type 'env t =
    | Glob_constr of Glob_term.glob_constr
    | Judgment of 'env Judgment.t

  let map f rhs =
    match rhs with
    | Glob_constr c -> Glob_constr c
    | Judgment j -> Judgment (Judgment.map f j)
end

module Clause = struct
  type ('env, 'tomatch_ind) desc = {
      env : 'env GlobalEnv.t;
      ids : Names.Id.Set.t;
      pats : 'tomatch_ind CasesPatterns.t;
      rhs : 'env Rhs.t;
    }

  type ('env, 'tomatch_ind) t = ('env, 'tomatch_ind) desc CAst.t

  let extract_pat_var (type env head tail)
      (clause : (env, head * tail) t) : Names.Name.t option =
    match clause.v.pats with
    | head :: _ -> CasesPattern.get_var head
end

module ReturnPred = struct
  type ('env, 'return_pred_height) t =
    | ReturnPred of ('env * 'return_pred_height) ETerm.t
    | Tycon of 'env ETerm.t option

  type ('a, 'b) map = {
      f : 'n . ('a * 'n) ETerm.t -> ('b * 'n) ETerm.t
    }

  let map (type a b height) (f : (a, b) map) (p : (a, height) t) :
      (b, height) t =
    match p with
    | ReturnPred t -> ReturnPred (f.f t)
    | Tycon o ->
        Tycon (Option.map
          (Eq.cast (Eq.arrow (ETerm.morphism Env.zero_r)
            (ETerm.morphism Env.zero_r)) f.f) o)
end

module PatternMatchingProblem = struct
  type ('env, 'tomatch_ind, 'eqn_length,
        'return_pred_height) t = {
      env : 'env GlobalEnv.t;
      tomatches :
        ('env, 'tomatch_ind, 'return_pred_height) TomatchVector.t;
      eqns :
        (('env, 'tomatch_ind) Clause.t, 'eqn_length) Vector.t;
      return_pred : ('env, 'return_pred_height) ReturnPred.t;
    }
end

module type MatchContextS = sig
  val typing_fun : compile_cases_typing_fun

  val style : Constr.case_style

  val program_mode : bool

  val compile_loop :
      ('env, 'tomatch_length, 'eqns_length, 'return_pred_height)
        PatternMatchingProblem.t -> 'env Judgment.t EvarMapMonad.t
end

let naming_of_program_mode (program_mode : bool) : Evarutil.naming_mode =
  if program_mode then ProgramNaming
  else KeepUserNameAndRenameExistingButSectionNames

module type CompilerS = sig
  val compile_cases :
      ?tycon:'env ETerm.t -> Constr.case_style -> 'env GlobalEnv.t ->
      Glob_term.glob_constr option ->
      Glob_term.tomatch_tuple list ->
      Glob_term.cases_clause list ->
      'env Judgment.t EvarMapMonad.t

  val compile_loop :
      ('env, 'tomatch_length, 'eqns_length, 'return_pred_height)
        PatternMatchingProblem.t -> 'env Judgment.t EvarMapMonad.t
end

module Make (MatchContext : MatchContextS) : CompilerS = struct
  module Typer = struct
    let judgment_of_glob_constr (type env) ?(tycon : env ETerm.t option)
        (env : env GlobalEnv.t)
        (constr : Glob_term.glob_constr) :
        (env Judgment.t) EvarMapMonad.t =
      Eq.cast (EvarMapMonad.eq (Eq.sym Judgment.eq))
        (fun (sigma : Evd.evar_map) ->
          MatchContext.typing_fun (Eq.cast (Eq.option ETerm.eq) tycon)
            (Eq.cast GlobalEnv.eq env) sigma
            constr)
  end

  module TypeTomatch (EqnLength : TypeS) = struct
    module PrepareTomatch = PrepareTomatch (EqnLength)

    let type_tomatch (glob_env : 'env GlobalEnv.t)
        (tomatch_with_pats :
           Glob_term.tomatch_tuple *
           (Glob_term.cases_pattern, EqnLength.t) Vector.t):
        'env PrepareTomatch.TomatchWithContext.exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let tomatch, pats = tomatch_with_pats in
      let term, predicate_pattern = tomatch in
      let* judgment = Typer.judgment_of_glob_constr glob_env term in
      let* sigma = EvarMapMonad.get in
      let env = GlobalEnv.env glob_env in
      PrepareTomatch.TomatchWithContext.make env sigma judgment
        predicate_pattern pats

    let type_tomatches
        (type tomatch_length)
        (env : 'env GlobalEnv.t)
        (tomatches_with_pats :
           (Glob_term.tomatch_tuple *
               (Glob_term.cases_pattern, EqnLength.t) Vector.t,
             tomatch_length) Vector.t) :
        ('env, tomatch_length)
        PrepareTomatch.TomatchWithContextVector.exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* vector =
        EvarMapMonad.vector_map (type_tomatch env) tomatches_with_pats in
      return (PrepareTomatch.TomatchWithContextVector.of_vector vector)
  end

  let compile_base (type env)
      (problem :
         (env, Nat.zero, _ Nat.succ, Nat.zero) PatternMatchingProblem.t) :
      env Judgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let env, rhs =
      match problem.eqns with
      | { v = { env; rhs; _ }} :: _ -> env, rhs in
    match rhs with
    | Glob_constr glob_constr ->
        begin match problem.return_pred with
        | Tycon tycon ->
            Typer.judgment_of_glob_constr ?tycon env glob_constr
        | ReturnPred return_pred ->
            let* judgment =
              Typer.judgment_of_glob_constr ~tycon:return_pred
                (Eq.cast (GlobalEnv.morphism (Eq.sym Env.zero_r)) env)
                glob_constr in
            let* (judgment, _trace) =
              Judgment.inh_conv_coerce_to
                ~program_mode:MatchContext.program_mode
                ~resolve_tc:true (GlobalEnv.env env)
                judgment return_pred in
            return (Judgment.morphism Env.zero_r judgment)
        end
    | Judgment judgment -> return judgment

  let is_compile_case_trivial
      (type env ind ind_tail eqns_length return_pred_height tail_height)
      (sigma : Evd.evar_map)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (tomatches : (env, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      ((Names.Name.t, eqns_length) Vector.t *
        (env, tail_height) ReturnPred.t) option =
    let open OptionMonad.Ops in
    let* vars = OptionMonad.vector_map Clause.extract_pat_var problem.eqns in
    let* () = match vars with [] -> None | _ :: _ -> Some () in
    let* return_pred =
      match problem.return_pred with
      | ReturnPred t ->
          if ETerm.noccur_between sigma 1
              (Height.to_int tomatch.return_pred_height) t then
            match Height.to_nat tomatch.return_pred_height with
            | Exists (nat, eq) ->
                let substl = ETerm.Substl.fake nat in
                let tail_height = TomatchVector.height tomatches in
                let t =
                  Eq.cast (ETerm.morphism (Eq.trans (Eq.sym Env.assoc)
                    (Env.pair (Env.pair Refl (Eq.sym eq)) Refl))) t in
                return (ReturnPred.ReturnPred
                  (ETerm.substnl substl tail_height t))
          else
            None
      | Tycon o -> return (ReturnPred.Tycon o) in
    return (vars, return_pred)

  let compile_case_trivial
      (type env ind ind_tail eqns_length return_pred_height tail_height)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (vars : (Names.Name.t, eqns_length) Vector.t)
      (return_pred : (env, tail_height) ReturnPred.t)
      (tomatches : (env, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      env Judgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    let self_name =
      try
        Vector.find (fun (name : Names.Name.t) -> name <> Anonymous) vars
      with Not_found -> Anonymous in
    let push name env =
      GlobalEnv.push_rel
        ~hypnaming:KeepUserNameAndRenameExistingButSectionNames sigma
        (Declaration.local_def (Context.annotR name) tomatch.judgment)
        env in
    let _declaration, env = push self_name problem.env in
    let tomatches =
      TomatchVector.map
        { f = fun t ->
          Tomatch.map (Term.lift Height.one) (ETerm.lift Height.one) t }
        tomatches in
    let eqns =
      Vector.map2
        (fun (var : Names.Name.t) ->
          CAst.map (fun (desc : (env, ind * ind_tail) Clause.desc) :
            (env * Nat.zero Nat.succ, ind_tail) Clause.desc ->
            let _, env = push var desc.env in
            let _ :: pats = desc.pats in
            let rhs = Rhs.map (ETerm.lift Height.one) desc.rhs in
            { env; ids = desc.ids; pats; rhs })) vars problem.eqns in
    let return_pred_eq (type a b c) () :
        (((a * b) * c) Env.t, ((a * c) * b) Env.t) Eq.t =
      Eq.trans Env.assoc
        (Eq.trans (Env.pair Refl Env.commut) (Eq.sym Env.assoc)) in
    let return_pred =
      ReturnPred.map { f = fun t ->
        Eq.cast (ETerm.morphism (return_pred_eq ()))
          (ETerm.lift Height.one t) } return_pred in
    let* judgment =
      MatchContext.compile_loop { env; tomatches; eqns; return_pred } in
    return
      (Judgment.map (ETerm.subst1 (Judgment.uj_val tomatch.judgment)) judgment)

  let compile_destruct
      (type env ind ind_tail eqns_length return_pred_height tail_height)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (ind : (env, ind) InductiveType.t)
      (tomatches : (env, ind_tail, tail_height) TomatchVector.t)
      (problem :
         (env, ind * ind_tail, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      env Judgment.t EvarMapMonad.t =
    let Exists family = InductiveType.to_inductive_family ind in
    let specif =
      InductiveSpecif.lookup (GlobalEnv.env problem.env)
        (InductiveFamily.to_inductive family) in
    let Exists constructors = InductiveSpecif.constructors specif in
    let nb_cstr = Tuple.length constructors in
    let branches = Tuple.make nb_cstr [] in
    let add_eqn (clause : (env, ind * ind_tail) Clause.t) =
      let open Tuple.Ops in
      let pat :: _ = clause.v.pats in
      match DAst.get (Eq.cast CasesPattern.eq pat) with
      | PatVar _ ->
          Tuple.iter branches (fun i ->
            branches.%(i) <- clause :: branches.%(i))
      | PatCstr (cstr, _, _) ->
          failwith "Not implemented" in
    failwith "Not implemented"

  let compile_case
      (type env tomatch_length eqns_length return_pred_height tail_height)
      (tomatch : (env, return_pred_height) Tomatch.t)
      (tomatches : (env, tomatch_length, tail_height) TomatchVector.t)
      (problem :
         (env, tomatch_length Nat.succ, eqns_length,
           return_pred_height * tail_height) PatternMatchingProblem.t) :
      env Judgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    match is_compile_case_trivial sigma tomatch tomatches problem with
    | Some (vars, return_pred) ->
        compile_case_trivial tomatch vars return_pred tomatches problem
    | None ->
        match tomatch.inductive_type with
        | Error _ -> assert false
        | Ok ind ->
            compile_destruct tomatch ind tomatches problem

  let compile_loop (type env tomatch_length eqns_length return_pred_height)
      (problem :
         (env, tomatch_length, eqns_length, return_pred_height)
         PatternMatchingProblem.t) :
      env Judgment.t EvarMapMonad.t =
    match problem.tomatches with
    | [] ->
        begin
          match problem.eqns with
          | [] -> assert false
          | _ :: _ -> compile_base problem
        end
    | tomatch :: tomatches ->
        compile_case tomatch tomatches problem

  let compile_cases (type env eqns_length)
      ?(tycon : env ETerm.t option)
      (style : Constr.case_style) (env : env GlobalEnv.t)
      (predopt : Glob_term.glob_constr option)
      (tomatches : Glob_term.tomatch_tuple list)
      (eqns : Glob_term.cases_clause list) :
      env Judgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* Exists tomatches = Typer.type_tomatches env tomatches eqns in
    let* sigma = EvarMapMonad.get in
    let return_pred_context, _ =
      TomatchWithContextVector.make_return_pred_context (GlobalEnv.env env)
        sigma tomatches in
    let hypnaming = naming_of_program_mode MatchContext.program_mode in
    let _, return_pred_env =
      GlobalEnv.push_rel_context ~hypnaming sigma return_pred_context env in
    let* return_pred =
      match predopt with
      | Some term ->
          let* judgment = Typer.judgment_of_glob_constr return_pred_env term in
          return (ReturnPred.ReturnPred (Judgment.uj_val judgment))
      | None -> return (ReturnPred.Tycon tycon) in
    let tomatches = TomatchWithContextVector.to_tomatch_vector tomatches in
    compile_loop { env; tomatches; return_pred; eqns }
end

let compile_cases ?loc ~(program_mode : bool) (style : Constr.case_style)
  ((typing_fun : compile_cases_typing_fun), (sigma : Evd.evar_map))
  (tycon : Evardefine.type_constraint) (env : GlobEnv.t)
    ((predopt : Glob_term.glob_constr option),
      (tomatchl : Glob_term.tomatch_tuples),
      (eqns : Glob_term.cases_clauses)) :
    Evd.evar_map * EConstr.unsafe_judgment =
  let open EvarMapMonad.Ops in
  let module Compiler = struct
    module rec Context : MatchContextS = struct
      let typing_fun = typing_fun
      let style = style
      let program_mode = program_mode
      let compile_loop = Compiler.compile_loop
    end
    and Compiler : CompilerS = Make (Context)
    include Compiler
  end in
  let env = Eq.cast (Eq.sym GlobalEnv.eq) env in
  let tycon = Option.map (Eq.cast (Eq.sym ETerm.eq)) tycon in
  sigma |>
  let* judgment =
    Compiler.compile_cases ?tycon style env predopt tomatchl eqns in
  return (Eq.cast Judgment.eq judgment)

let constr_of_pat :
           Environ.env ->
           Evd.evar_map ->
           EConstr.rel_context ->
           Glob_term.cases_pattern ->
           Names.Id.Set.t ->
           Evd.evar_map * Glob_term.cases_pattern *
           (EConstr.rel_context * EConstr.constr *
            (EConstr.types * EConstr.constr list) * Glob_term.cases_pattern) *
           Names.Id.Set.t =
    fun _ -> failwith "Not_implemented"

type 'a rhs =
    { rhs_env    : GlobEnv.t;
      rhs_vars   : Names.Id.Set.t;
      avoid_ids  : Names.Id.Set.t;
      it         : 'a option}

type 'a equation =
    { patterns     : Glob_term.cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : Names.Name.t list;
      eqn_loc      : Loc.t option;
      used         : bool ref }

type 'a matrix = 'a equation list

type tomatch_type =
  | IsInd of EConstr.types * Inductiveops.inductive_type * Names.Name.t list
  | NotInd of EConstr.constr option * EConstr.types

type tomatch_status =
  | Pushed of (bool*((EConstr.constr * tomatch_type) * int list * Names.Name.t))
  | Alias of
      (bool *
         (Names.Name.t * EConstr.constr * (EConstr.constr * EConstr.types)))
  | NonDepAlias
  | Abstract of int * EConstr.rel_declaration

type tomatch_stack = tomatch_status list

type pattern_history =
  | Top
  | MakeConstructor of Names.constructor * pattern_continuation

and pattern_continuation =
  | Continuation of int * Glob_term.cases_pattern list * pattern_history
  | Result of Glob_term.cases_pattern list

type 'a pattern_matching_problem =
    { env       : GlobEnv.t;
      pred      : EConstr.constr;
      tomatch   : tomatch_stack;
      history   : pattern_continuation;
      mat       : 'a matrix;
      caseloc   : Loc.t option;
      casestyle : Constr.case_style;
      typing_function: Evardefine.type_constraint -> GlobEnv.t -> Evd.evar_map -> 'a option -> Evd.evar_map * EConstr.unsafe_judgment }

let compile : program_mode:bool -> Evd.evar_map -> 'a pattern_matching_problem -> Evd.evar_map * EConstr.unsafe_judgment =
    fun ~program_mode _ -> failwith "Not_implemented"

let prepare_predicate : ?loc:Loc.t -> program_mode:bool ->
           (Evardefine.type_constraint ->
            GlobEnv.t -> Evd.evar_map -> Glob_term.glob_constr -> Evd.evar_map * EConstr.unsafe_judgment) ->
           GlobEnv.t ->
           Evd.evar_map ->
           (EConstr.types * tomatch_type) list ->
           EConstr.rel_context list ->
           EConstr.constr option -> Glob_term.glob_constr option -> (Evd.evar_map * (Names.Name.t * Names.Name.t list) list * EConstr.constr) list =
    fun ?loc ~program_mode _ -> failwith "Not_implemented"

let make_return_predicate_ltac_lvar : GlobEnv.t -> Evd.evar_map -> Names.Name.t ->
  Glob_term.glob_constr -> EConstr.constr -> GlobEnv.t =
    fun _ -> failwith "Not_implemented"
