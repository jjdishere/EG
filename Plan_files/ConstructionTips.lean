/-
# Tips for creating a file in construction

## File Structure
The following assumes that there is a single new concept to define in the file. If a file contains more the 2 new concept to define (e.g. angle bis and incenter are in the same file), please expand each of them following this instruction.

Broadly speaking, there are three kind of new concepts in Construction: A new class (e.g. Quadrilateral), A new construction (e.g. AngleBis), A new property alone (e.g. IsParallelogram).

1. (only for class/construction) Prove the preparing theorems and define the class/construction;
2. (only for class) Define the make methods;
3. Define the predicate (e.g. IsAngleBis IsParallelogram), if your new class extends some old class by adding new properties, you may also need to define a predicate `before` you can define thr class (e.g. Quadrilaterial.IsConvex);
4. (only for class/construction) Compatibility of the predicate and your class/construction;
5. Criterion: theorems with your predicate (construction)/ structure (class) in the conclusion;
6. Properties: theorems with your predicate (class)/ structure (class) in the condition.

## Minor Principles

1. We should stick to geometry as much as possible. Please avoid using vector calculations as possible. As a result, one avoids stating theorems using `Vec` or `VecND` (either in conditions or conclusions).

2. If you are formulating theorems of a class, please ensure your theorems has a version stated in terms of `structure` you defined, not only state in terms of point. But it is ok to have another version of theorem stated.

3.

-/
