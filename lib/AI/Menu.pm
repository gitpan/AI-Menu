package AI::Menu;

use vars qw: $VERSION :;

$VERSION = 0.01;

package AI::Menu::Factory;

use Class::MethodMaker
        new_with_init => 'new',
        code => [ qw: weight_f leaf_q : ],
        get_set => [ qw: width maker : ],
    ;
use Graph::Directed;
use strict;

$AI::Menu::Factory::default_weight_f = sub {      
    my($self, $G, $u, $v) = @_;
    no warnings;
    return( ($self->{width}-1-$G -> out_degree($u))**2
        + (2*($G -> in_degree($v)))**2  
        + (2*(1-$G->in_degree($u)))**2);  
};

$AI::Menu::Factory::default_leaf_q = sub { 0 };

sub init {
    my($self, %args) = @_;

    @$self{keys %args} = values %args;
 
    $self -> {width} ||= 3;

    $self -> {leaf_q} = $AI::Menu::Factory::default_leaf_q
        unless defined $self -> {leaf_q};

    $self -> {weight_f} = $AI::Menu::Factory::default_weight_f 
       unless defined $self -> {weight_f};

    $self -> {maker} ||= 'AI::Menu::Maker';
   
    return $self;
}

sub generate {
    my $self = shift;

    return unless @_;

    my $leafq;
   my $g;

    if(ref $_[0] eq 'HASH') {
        my %functions;
        @functions{keys %{$_[0]}} = ();
        $leafq = sub { exists $functions{$_[0]} };
        $g = new Graph::Directed;
        foreach my $f (keys %{$_[0]}) {
            $g -> add_edges(map { ($_, $f) } @{$_[0]->{$f} || []} );
        }
        shift;
        if(@_) {
            my $c = shift;
            foreach my $f (keys %$c) {
                $g -> add_edges(map { ($f, $_) } @{$c->{$f} || []} );
            }
        } else {
            my $v;
            foreach my $u ($g -> vertices()) {
                my @edges = $g -> out_edges($u);
                while(($v, $v) = splice @edges, 0, 2) {
                    foreach my $t ($g -> in_edges($v)) {
                        $g -> add_edge($u, $t) unless
                            $g -> has_edge($u, $t);
                     }
                }
            }
        }
    } else {
        $leafq = $self -> leaf_q;
        $g = shift;
    }

    my $menu = $self -> {maker} -> new(
        width => $self->{width},
        weight_f => $self -> {weight_f},
        leaf_q => $leafq,
    );

    my $optscore = 1;

    return $menu -> generate_tree($g, $optscore);
}

package AI::Menu::Maker;

use 5.005_003;
use strict;
use Class::MethodMaker
        new_with_init => 'new',
    ;
use Tree::Nary;

sub init { 
    my($self, %args) = @_;

    @$self{keys %args} = values %args;

    $self -> {width} ||= 3;

    return $self;
}

sub generate_tree {
    my($self, $g, $optscore) = @_;

    my($cand, $maxscore, $start) = $self -> calculate_optimum_tree($g, $optscore);

    return $self -> create_data_tree($cand, $start);
}

sub create_data_tree {
    my($self, $g, $start) = @_;

    my($tree, @E) = ( new Tree::Nary($start), $g -> out_edges($start));

    for(my $i = 1; $i < @E; $i+=2) {
        $tree -> insert($tree, -1, $self -> create_data_tree($g, $E[$i]));
    }

    return $tree;
}

sub score {
    my $self = shift;
    my $g = shift;
    my $width = $self -> {width};

    return 0 unless @_;

    my @out = map $g->out_edges($_), @_;
    @out = map $out[$_*2+1], 0..@out/2-1;

    return scalar(@out) 
         * ((($self -> score($g,@out)||0
             ) / $width ) || 1
           ) /  $width;
}

sub MST {
   my($self, $G, $weight, $start) = @_;
   my $MST = (ref $G) -> new();
   my @E = $G -> edges;
   my ($Wn, $W, $u, $v, $w) = ([],[]);

   my $width = $self -> {width} - 1;

   $MST -> add_vertex( $start );

   while (($u, $v) = splice(@E, 0, 2)) {
      $w = &$weight($self, $G, $u, $v);
      next unless defined $w; 
      push @$Wn, [ $u, $v, $w ];
   }

   $MST->directed( $G->directed );

   @$Wn = sort { $a->[ 2 ] <=> $b->[ 2 ] } @$Wn;
   while(@$Wn != @$W) {
      $W = $Wn; $Wn = [ ];
      foreach my $e ( @$W ) {
         ($u, $v, $w) = @$e;
         next if $MST->has_vertex($v);
         unless($MST->has_vertex($u)) {
             push @$Wn, $e;
             next;
         }
         next if $MST->out_degree($u)>$width;
         $MST->add_weighted_edge($u,$w,$v);
      }
   }

   return $MST;
}


sub compress {
    my($self, $g, @o, @i) = @_;

    my(@v) = map { $_->[1] } 
               sort { $a->[0] <=> $b->[0] }
                 map { [ $g -> out_degree($_) - $g -> in_degree($_), $_ ] }
                     $g -> vertices;

    my $leafq = $self -> {leaf_q};

    foreach my $v (@v) {
        @o = $g -> out_edges($v);
        next if @o > 2;
        if(@o) {
            @i = $g -> in_edges($v);

            $g -> delete_edges(@o, @i);
            $g -> delete_vertex($v);

            $g -> add_edges(map { ($i[$_*2], $o[1]) }
                                0..@i/2-1);
        } elsif(!&$leafq($v)) {
            $g -> delete_vertex($v);
        }
    }
    $g;
}

sub _calculate_optm_tree {
    my($self, $cg, $start, $goal) = @_;
    my($maxscore, $candidate, $s, $mst, $mst2) = (-1);

    my $leafq = $self -> {leaf_q};
    my $width = $self -> {width};

    my $leafs = grep &$leafq($_), $cg -> vertices;

    $mst = $self -> compress( $self -> MST($cg, sub { &{shift -> {weight_f}}(@_) }, $start) );

    $mst2 = $mst -> copy();

    my $weight_function  = sub { &{$_[0] -> {weight_f}}($_[0],$mst , @_[2,3]) }; 
    my $weight_function2 = sub { &{$_[0] -> {weight_f}}($_[0],$mst2, @_[2,3]) }; 
    
    until($mst->eq($mst2)) {
        $mst  = $self -> compress( $self -> MST($cg, $weight_function , $start));
        $mst2 = $self -> compress( $self -> MST($cg, $weight_function2, $start));
    }

    do {
        $mst  = $self -> compress( $self -> MST($cg, $weight_function , $start));
        $mst2 = $self -> compress( $self -> MST($cg, $weight_function2, $start));
        $mst2 = $self -> compress( $self -> MST($cg, $weight_function2, $start));

        if($leafs == grep &$leafq($_), $mst -> vertices) {
            $s = $self -> score($mst, $start);
            ($maxscore, $candidate) = ($s, $mst) 
                if $s > $maxscore;
            return ($candidate, $maxscore)
                if defined $goal and $goal <= $maxscore;
        }
    } until($mst->eq($mst2));
    return ($candidate, $maxscore);
}

sub calculate_optimum_tree {
    my $self = shift;
    my $g = shift;
    my $goal = shift || 1;

    my($maxscore, $cand, $start) = (-1);

    foreach my $v ($g -> vertices()) {
        next unless $g -> out_degree($v);
        my($candidate, $score) = 
            $self -> _calculate_optm_tree($g, $v, $goal);
        ($maxscore, $cand, $start) = ($score, $candidate, $v) 
            if $score > $maxscore;
        return ($cand, $maxscore, $start)
            if defined $goal and $goal <= $maxscore;
    }

    return($cand, $maxscore, $start);
}


1;

__END__

=head1 NAME

AI::Menu

=head1 SYNOPSIS

 use AI::Menu;

 my $factory = new AI::Menu::Factory;

 my $menu = $factory->generate($hash_of_functions);
 my $menu = $factory->generate($hash_of_functions, $hash_of_categories);
 my $menu = $factory->generate($graph);

=head1 DESCRIPTION

An C<AI::Menu::Factory> object generates C<Tree::Nary> objects from directed
graphs (L<Graph::Directed|Graph::Directed> or an object with the same
methods) or a description of the function set.

The algorithm is not very efficient (approximately O(F^6), F being the
number of functions).  It is also not quite as intelligent as it should be.
You should cache the results instead of repeatedly calculating them.

As the algorithm is optimized or more efficient algorithms are found, they
will be incorporated.  The interface for generating the trees should not
change too much.  The resulting object might become a L<Tree::Nary|Tree::Nary>
object encased in an L<AI::Menu|AI::Menu> object.

=head1 METHODS

All of the following methods (except generate) are available in the C<new>
function when creating the C<AI::Menu::Factory> object.

=over 4

=item generate

This function does some housekeeping before calling a configurable module
to generate the tree.

If called with a single hash reference, the hash is assumed to be a list of
functions mapping to array references containing a list of categories.  It
is further assumed that the sets of function names and category names are
disjoint.  A closure is created for the C<leaf_q> function which returns
true if its argument is a key in the hash reference.  The complete graph is
created from this single hash reference: if a category can reach another
category through a function, then an edge is inserted between the two
categories.  This edge is bidirectional.

If called with two hash references, the first hash is treated as before,
but the second hash reference is considered a mapping of categories to
categories.  This second hash is used instead of automatically generating
the information from the first hash.

If called with a single object that is not a hash reference, then the
argument is considered a graph object (usually of
L<Graph::Directed|Graph::Directed>).  The C<leaf_q> function will need to
be defined.

=item leaf_q

This function returns true if the argument represents a function (leaf in
the graph).  It returns false if the argument represents a category.  This
may be set either when the C<AI::Menu::Factory> object is created or
through a method call.  The method call with no argument returns the
current function.

=item maker

This is the package used to create the menu from the graph.  The following
call is made:

     my $menu = $self -> {maker} -> new(
         width => $self->{width},
         weight_f => $self -> {weight_f},
         leaf_q => $leafq,
     );
     
     return $menu -> generate_tree($g, $optscore);

The C<$optscore> value is the score for the optimum tree.  Once a tree is
found with this score, searching should stop.

=item new

Creates an C<AI::Menu::Factory> object.  Optional arguments are key/value
pairs taken from this list of methods except for C<generate> and C<new>.

=item weight_f

This function is used to calculate the edge weights in the graph.  It is
called with four arguments: the object generating the tree, the graph
object, the originating vertex, the destination vertex.  The function
should return C<undef> for an infinite weight.

=item width

This is the desired number of children per node.  The optimal number (and
default) is three.

=back 4

=head1 EXAMPLE

The following example illustrates generating a menu from a list of
functions and printing the resulting tree using LaTeX.

 my $factory = AI::Menu::Factory;

 my $functions = {
    a => [qw: A B D :],
    b => [qw: C D E :],
    c => [qw: A B C :],
    d => [qw: E G H :],
    e => [qw: A C E :],
    f => [qw: A D F :],
 };

 $menu = $factory -> generate($functions);

 # following borrowed from Tree::Nary's test.pl
 sub node_build_string() {
    my ($node, $ref_of_arg) = (shift, shift);
    my $p = $ref_of_arg;
    my $string;
    my $c = $node->{data};

    if(defined($p)) {
       $string = $$p;
    } else {
       $string = "";
    }
    
    if($node -> is_leaf($node)) {
       $c = "\\leaf{\\mbox{ $c }}\n";
    } else {
       $c = "\\branch{" . $node -> n_children( $node ) . "}{$c}\n";
    }
    
    $string .= $c;
    $$p = $string;
    
    return($Tree::Nary::FALSE);
 }
 
 my $string;
 
 $menu -> traverse( $menu,  
                    $Tree::Nary::POST_ORDER,
                    $Tree::Nary::TRAVERSE_ALL, -1,
                    \&node_build_string, \$string);
 
 print "$string\n";

The above code prints out the following:

 \leaf{\mbox{ a }}
 \leaf{\mbox{ c }}
 \branch{2}{B}
 \leaf{\mbox{ b }}
 \leaf{\mbox{ d }}
 \leaf{\mbox{ e }}
 \branch{3}{C}
 \leaf{\mbox{ f }}
 \branch{3}{A}

This corresponds to the following tree:

        A
     /  |  \
    f   C   B
       /|\  |\
      b d e c a

=head1 BUGS

The optimal score is fixed at one.  This means all possibilities are
searched each time.  We need an algorithm that maps number of functions to
optimal score for a tree with arbitrary $width parameter.

While the algorithm seems inefficient, I am not aware of how far it is from
most efficient.  Some work remains in this area.

The tree can be a bit strange.  In fact, it usually is.  The results should
be considered academic or just hints at this point.  If you have an
interesting set of functions and categories, send them to me.

The algorithm needs some way to make certain categories more important than
others.

=head1 SEE ALSO

L<Graph::Directed>,
L<Tree::Nary>.

=head1 AUTHOR

James Smith <jgsmith@jamesmith.com>

=head1 COPYRIGHT

Copyright (C) 2001 Texas A&M University.  All Rights Reserved.
 
This module is free software; you can redistribute it and/or
modify it under the same terms as Perl itself.
