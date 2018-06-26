/*******************************************************************
 *     This is part of Aerial, it is distributed under the         *
 *  terms of the GNU Lesser General Public License version 3       *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2017:                                                *
 *  Dmitriy Traytel (ETH Zürich)                                   *
 *******************************************************************/

%{
open Util
open Explanator
%}

%token <string> ATOM
%token LOPEN ROPEN
%token FALSE TRUE NEG CONJ DISJ IMP IFF EQ NEQ EOF
%token SINCE UNTIL WUNTIL RELEASE TRIGGER
%token NEXT PREV ALWAYS EVENTUALLY HISTORICALLY ONCE

%nonassoc PREV NEXT ALWAYS EVENTUALLY ONCE HISTORICALLY
%nonassoc SINCE UNTIL WUNTIL RELEASE TRIGGER
%right IFF
%right IMP
%left DISJ
%left CONJ
%nonassoc NEG

%type <Explanator.formula> formula
%start formula

%%

formula:
| e EOF { $1 }

e:
| LOPEN e ROPEN           { $2 }
| TRUE                    { tt }
| FALSE                   { ff }
| e CONJ e                { conj $1 $3 }
| e DISJ e                { disj $1 $3 }
| e IMP e                 { impl $1 $3 }
| e IFF e                 { iff $1 $3 }
| NEG e                   { neg $2 }
| ATOM                    { p $1 }
| ATOM EQ ATOM            { p ($1 ^ "=" ^ $3) }
| ATOM NEQ ATOM           { neg (p ($1 ^ "=" ^ $3)) }
| e SINCE e               { since $1 $3 }
| e TRIGGER e             { trigger $1 $3 }
| e UNTIL e               { until $1 $3 }
| e WUNTIL e              { weak_until $1 $3 }
| e RELEASE e             { release $1 $3 }
| NEXT e                  { next $2 }
| PREV e                  { prev $2 }
| ONCE e                  { once $2 }
| HISTORICALLY e          { historically $2 }
| ALWAYS e                { always $2 }
| EVENTUALLY e            { eventually $2 }
