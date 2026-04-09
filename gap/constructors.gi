#############################################################################
##
##  constructors.gi
##  Copyright (C) 2019                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains constructions of certain types of digraphs, from other
# digraphs.

InstallMethod(BipartiteDoubleDigraph, "for a mutable digraph by out-neighbours",
[IsMutableDigraph and IsDigraphByOutNeighboursRep],
function(D)
  local list, N, i, j;
  list := D!.OutNeighbours;
  N    := Length(list);
  Append(list, List([1 .. N], x -> []));
  for i in [1 .. N] do
    for j in [1 .. Length(list[i])] do
      list[i + N][j] := list[i][j];
      list[i][j]     := list[i][j] + N;
    od;
  od;
  return D;
end);

InstallMethod(BipartiteDoubleDigraph, "for an immutable digraph",
[IsImmutableDigraph],
function(D)
  local C, X, N, p;
  C := MakeImmutable(BipartiteDoubleDigraph(DigraphMutableCopy(D)));
  if HasDigraphGroup(D) then
    X := GeneratorsOfGroup(DigraphGroup(D));
    N := DigraphNrVertices(D);
    p := PermList(Concatenation([1 .. N] + N, [1 .. N]));
    X := List(X, x -> x * (x ^ p));
    Add(X, p);
    SetDigraphGroup(C, Group(X));
  fi;
  return C;
end);

InstallMethod(DoubleDigraph, "for a mutable digraph by out-neighbours",
[IsMutableDigraph and IsDigraphByOutNeighboursRep],
function(D)
  local list, N, i, j;
  list := D!.OutNeighbours;
  N    := Length(list);
  Append(list, list + N);
  for i in [1 .. N] do
    for j in [1 .. Length(list[i])] do
      Add(list[i + N], list[i][j]);
      Add(list[i], list[i][j] + N);
    od;
  od;
  return D;
end);

InstallMethod(DoubleDigraph, "for an immutable digraph",
[IsImmutableDigraph],
function(D)
  local C, X, N, p;
  C := MakeImmutable(DoubleDigraph(DigraphMutableCopy(D)));
  if HasDigraphGroup(D) then
    X := GeneratorsOfGroup(DigraphGroup(D));
    N := DigraphNrVertices(D);
    p := PermList(Concatenation([1 .. N] + N, [1 .. N]));
    X := List(X, x -> x * (x ^ p));
    Add(X, p);
    SetDigraphGroup(C, Group(X));
  fi;
  return C;
end);

InstallMethod(DistanceDigraph,
"for a mutable digraph by out-neighbours and a list of distances",
[IsMutableDigraph and IsDigraphByOutNeighboursRep, IsList],
function(D, distances)
  local list, x;
  # Can't change D!.OutNeighbours in-place, since it is used by
  # DigraphDistanceSet
  list := EmptyPlist(DigraphNrVertices(D));
  for x in DigraphVertices(D) do
    list[x] := DigraphDistanceSet(D, x, distances);
  od;
  D!.OutNeighbours := list;
  return D;
end);

InstallMethod(DistanceDigraph,
"for an immutable digraph and a list of distances",
[IsImmutableDigraph, IsList],
function(D, distances)
  local list, G, o, rem, sch, gen, record, rep, g, C, x;
  if HasDigraphGroup(D) and not IsTrivial(DigraphGroup(D)) then
    list := EmptyPlist(DigraphNrVertices(D));
    G := DigraphGroup(D);
    o := DigraphOrbitReps(D);
    for x in o do
      list[x] := DigraphDistanceSet(D, x, distances);
    od;
    rem := Difference(DigraphVertices(D), o);
    sch := DigraphSchreierVector(D);
    gen := GeneratorsOfGroup(G);
    for x in rem do
      record  := DIGRAPHS_TraceSchreierVector(gen, sch, x);
      rep     := o[record.representative];
      g       := DIGRAPHS_EvaluateWord(gen, record.word);
      list[x] := List(list[rep], x -> x ^ g);
    od;
    C := DigraphNC(list);
  else
    C := MakeImmutable(DistanceDigraph(DigraphMutableCopy(D), distances));
  fi;
  SetDigraphGroup(C, DigraphGroup(D));
  return C;
end);

InstallMethod(DistanceDigraph, "for a digraph and an integer",
[IsDigraph, IsInt],
function(D, distance)
  if distance < 0 then
    ErrorNoReturn("the 2nd argument <distance> must be a non-negative ",
                  "integer,");
  fi;
  return DistanceDigraph(D, [distance]);
end);

# Warning: unlike the other methods the next two do not change their arguments
# in place, and always return an immutable digraph. There is currently no
# method for creating a mutable digraph with 4 arguments, as required by the
# next two methods.

InstallMethod(LineDigraph, "for a digraph", [IsDigraph],
function(D)
  local G, opt;
  if HasDigraphGroup(D) then
    G := DigraphGroup(D);
  else
    G := Group(());
  fi;
  if IsMutableDigraph(D) then
    opt := IsMutableDigraph;
  else
    opt := IsImmutableDigraph;
  fi;
  return Digraph(opt,
                 G,
                 DigraphEdges(D),
                 OnPairs,
                 {x, y} -> x <> y and x[2] = y[1]);
end);

InstallMethod(LineUndirectedDigraph, "for a digraph", [IsDigraph],
function(D)
  local G, opt;
  if not IsSymmetricDigraph(D) then
    ErrorNoReturn("the argument <D> must be a symmetric digraph,");
  elif HasDigraphGroup(D) then
    G := DigraphGroup(D);
  else
    G := Group(());
  fi;
  if IsMutableDigraph(D) then
    opt := IsMutableDigraph;
  else
    opt := IsImmutableDigraph;
  fi;
  return Digraph(opt,
                 G,
                 Set(DigraphEdges(D), Set),
                 OnSets,
                 {x, y} -> x <> y and not IsEmpty(Intersection(x, y)));
end);


InstallMethod(BayesianNetwork, "for a digraph and a list of CPT matrices", [IsDigraph, IsList],
function(D, CPT) 
  if not DigraphNrVertices(D) = Length(CPT) then
    ErrorNoReturn("length of probability list must be equal to number of vertices");
  # Need to change this to check BN is polytree (the underlying undirected graph is acylic)
  elif not IsAcyclicDigraph(D) then
    ErrorNoReturn("Digraph must be Acylic");
  fi;
  # Check that every row of all CPTs sum to 1

  # Check that every CPT for node n has dimension: 2 x 2 ^ {size(InNeighbours(D)[n]))

  # Set the label of every node as the CPT matrix
  SetDigraphVertexLabels(D, CPT);
  return D;
end);

InstallMethod(BeliefPropagation, "for a BN, target vertexInt and list of evidence",[IsDigraph, IsInt, IsList],
function(BN, X, e)
  local priors, likelihoods, unnormalized, sum, 
  initialise_likelihood_and_prior, get_likelihood, get_prior,
  message_to_parent, message_to_child;

  initialise_likelihood_and_prior := function(e)
    local i, n, pair, evidence_lookup;

    n := DigraphNrVertices(BN);
    priors := List([1..n], i -> fail);
    likelihoods := List([1..n], i -> fail);

    # used to determine for every node, if it is observed and if it is stores it's value
    evidence_lookup := List([1..n], i -> fail);

    for pair in e do
      evidence_lookup[pair[1]] := pair[2];
    od;

    for i in [1..n] do
      if evidence_lookup[i] <> fail then
        if evidence_lookup[i] = true then
          priors[i] := [1,0];
          likelihoods[i] := [1,0];
        else
          priors[i] := [0,1];
          likelihoods[i] := [0,1];
        fi;
      # check if root node (no parents) or leaf node (no children)
      elif Length(InNeighbours(BN)[i]) = 0 then
        priors[i] := DigraphVertexLabel(BN,i)[1];

      elif Length(OutNeighbours(BN)[i]) = 0 then
        likelihoods[i] := [1, 1];
      fi;
    od;
  end;

  get_likelihood := function(X)
    local messages, c;
    if likelihoods[X] <> fail then
      return likelihoods[X];
    fi;

    messages := [];
    
    for c in OutNeighbours(BN)[X] do
      Add(messages, message_to_parent(c, X));
    od;
    likelihoods[X] := [Product(TransposedMat(messages)[1]), Product(TransposedMat(messages)[2])];
    return likelihoods[X];
  end;

  get_prior := function(X)
    local messages, p;
    if priors[X] <> fail then
      return priors[X];
    fi;
    messages := [];
    for p in InNeighbours(BN)[X] do
      Add(messages, message_to_child(p, X));
    od;
    # update this line later to combine multiple pi messages in
    priors[X] := messages[1];
    return priors[X];
  end;

  message_to_parent := function(child, parent)
    local likelihood_child, likelihood_parent;
    likelihood_child := get_likelihood(child);
    # performs matrix multiplication of CPT and column vector λ
    likelihood_parent := List(DigraphVertexLabel(BN,child), row -> row * likelihood_child);
    return likelihood_parent;
  end;

  message_to_child := function(parent, child)
    local prior_parent, prior_child, CPT;
    prior_parent := get_prior(parent);
    CPT := DigraphVertexLabel(BN,child);
    # performs matrix multiplication of row vector pi and CPT
    prior_child := List(TransposedMat(CPT), col -> prior_parent * col);
    return prior_child;
  end;

  initialise_likelihood_and_prior(e);

  unnormalized := List([1..2], i -> get_prior(X)[i] * get_likelihood(X)[i]);  
  
  sum := Sum(unnormalized);

  # Print("Priors: ",priors, "\n");
  # Print("Likelihoods: ",likelihoods);

  return List(unnormalized, x -> x/sum);
end);

InstallMethod(GetCPT, "for a BN and vertexInt", [IsDigraph, IsInt],
function(BN, n)
  return DigraphVertexLabel(BN,n);
end);
