use ExtUtils::MakeMaker;
# $Id: Makefile.PL,v 1.1 2001/11/19 17:52:53 jgsmith Exp $

WriteMakefile( NAME => 'AI::Menu',
               VERSION_FROM => 'lib/AI/Menu.pm',
               PREREQ_PM =>    { Graph => 0.201,
                                 Class::MethodMaker => 1.02,
                                 Tree::Nary => 1.21,
                               },
               dist         => { COMPRESS => 'gzip -9f', SUFFIX => 'gz', },
             );
