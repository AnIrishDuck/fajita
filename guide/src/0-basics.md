# Understanding CSG

A concise lay definition of CSG could be "math with shapes and solids".
Despite this simple description, CSG is a powerful and useful tool at the
heart of modern CAD and CAM programs.

There are three core CSG operations:

- Finding the _union_ of two objects.
- Finding the _intersection_ of two objects.
- _Subtraction_ of one object from another.

| ![Common CSG Operations](./0-ops.png) |
|:--:|
| _The union, intersection, and difference of two squares_ |

I have been unable to find good online resources describing how these
operations work. That is not to say that none exist. This guide itself
draws heavily on the amazing documentation provided by CGAL and CSG.js
However, each of these sources have their own flaws.

CSG.js has an in-depth guide to _how_ it works, but is light on the theory
and _why_ it works.

The CGAL CSG library has a very theory-centric description that leans heavily
on theoretical concepts like Nef Polyhedra. This resource was hard to
decipher, but was very helpful in my eventual understanding of the
foundational math behind CSG.

This guide will attempt to strike a happy medium. We'll address philisophical
questions like "what is a solid?" and "what is a shape?" while also
describing how to model them and, eventually, how to do "math" with them.

We will start with two dimensions, because it is easier to visualize and
reason about. However, in the final sections we will see how it is easy to
extend the core concepts we describe to the third dimension.

### What are Things?

We formally define shapes and solids as "containers of points". Specifically,
for our analysis, we consider such containers as dividing points (and later,
some other objects) into three categories:

- Things that are _in_ the container.
- Things that are _on_ the container.
- Things that are _out_ of the container.

These roughly correspond to `<`, `=`, and `>` that we know and love from the
familiar world of numbers.

### Representing Containers

It is tempting to immediately jump from this definition to the mathematical
world of equations. Implicit functions take this idea to its logical and
beautiful conclusion. They use inequalities like `x * x < 1` to define the
container relationship (in this case, describing a circle).

|![An implicit circle](./0-implicit-circle.png)|
|:--:|
|_An implicit representation of a circle_|

While the results are often seductively simple definitions of complex
objects, these representations are not well-suited for computational
manipulation.

The blunt reason why is that actually solving the equations these functions
produce in an algorithmic way is incredibly complicated. A large volume of
academic papers have been written in service of this problem.

### Approximating Beauty

Instead, we will center our discussion around linear approximations of these
amazing objects. While uglier, the results are much more tractable.

|![A linear approximation of the circle](./0-linear-circle.png)|
|:--:|
|_A linear approximation of the previous circle_|

We can then take an inductive approach to defining and solving our problem.
This journey will see us build increasingly useful abstractions and
operations on them until the tools we've built can be used to perform CSG
operations in a straightforward way.

It all starts with a line.

### Halfspaces All The Way Down

The simplest possible container in euclidean spaces is the halfspace. A
halfspace is a linear division of every point in the space.

Implicit definitions of halfspaces are easy to understand. They are simple
linear inequalities: `x > 5` and `x + y < 4` are examples. Taking a point and
plugging it in to the equation yields an obvious result for whether a point
is within or without.

|![Implicit halfspaces](./0-implicit-line.png)|
|:--:|
|_Implicit linear inequalities_|

A more explicit definition is the segment-normal approach. A segment is
extended to an infinite line to form the partition. The normal vector is
included to orient this line and define which points lie "outside" the
halfspace.

|![Segment-normal halfspaces](./0-explicit-edge.png)|
|:--:|
|_Segment-normal representations of halfspaces_|

The normal vector is always perpendicular to the given segment. This lets us
easily calculate whether a given point is _in_, _on_, or _out_ of the
partition via the dot product.

### Edges Contain Points

We will call this segment-normal object an _edge_. Each edge has a halfspace,
and storing the two endpoints explicitly will come in handy later.

The normal vector traditionally defines points "outside" the partition. This
makes it easy to calculate whether a given point is contained by the
halfspace via the dot product. This lets us then determine whether a given point
is inside, on, or outside the partition.

|![An edge and some relative points](./0-edge-contains.png)|
|:--:|
|_An edge and points (a) in, (b) on, and (c) out of it_|

Note the angle that each point forms with the normal in the above diagram.
Points "inside" form an angle greater than 90 degrees, points "on" form an
angle exactly 90 degrees, and points "outside form an angle less than 90
degrees.

This corresponds to a dot product of -1, 0, and 1 respectively. This is the
only math that we'll need to use for the entirety of this guide.

### The Subtle Knife

Because edges contain points, one natural next question is whether edges can
contain other edges.

The answer is "not quite". Consider that an edge itself consists of two
points. This necessarily means that one `knife` edge cannot necessarily
contain another `target` edge. Sure, if both points of the `target` are
inside the `knife`'s halfspace, then we can say the `target` is _in_ the
`knife`. The same logic applies if the target is _out_ of the knife.

But what if one point is _in_ and the other is _out_?

In this case, we say the `knife` "cuts" the `target`. The result of this cut
is one or zero _in_ edges, one or zero _on_ intersection points (or edges),
and one or zero _out_ edges. This concept is incredibly powerful, and one
we'll extend to more complex objects.

|![One edge cutting another](./0-edge-knife.png)|
|:--:|
|_One edge cuts another into (a) in, (b) on, and (c) out parts_|

To generalize, we'll say that any `knife` object _cuts_ a `target` object by
producing an _in_ part, an _on_ part, and an _out_ part. All outputs of the
operation must be either _in_ or _on_ the original target.

### Sets of Edges

So, we've met the foundational building block of our world, the edge. We've
also observed how it can function as a "knife" that cuts other objects.
Despite this superpower, the edge object is still incredibly simple. In the
next section, we'll see how we can cook up more interesting things with this
humble ingredient.
