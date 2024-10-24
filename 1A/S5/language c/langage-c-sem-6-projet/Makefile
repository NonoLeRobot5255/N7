# This file is part of dijkstra.
# 
# dijkstra is free software: you can redistribute it and/or modify it under 
# the terms of the GNU General Public License as published by the Free Software 
# Foundation, either version 3 of the License, or (at your option) any later 
# version.
# 
# dijkstra is distributed in the hope that it will be useful, but WITHOUT ANY 
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
# A PARTICULAR PURPOSE. See the GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License along with 
# dijkstra. If not, see <https://www.gnu.org/licenses/>.
#
# dijkstra - Copyright (c) 2024 Guillaume Dupont
# Contact: <guillaume.dupont@toulouse-inp.fr>
CC=gcc
SDL=/mnt/n7fs/ens/tp_dupont/clibs/SDL2
CFLAGS_D=-g -Wall -Wextra -pedantic -O0 -D_REENTRANT -D_DEBUG -DSTRICT_THREADING -I$(SDL)
CFLAGS=-Wall -Wextra -O2 -D_REENTRANT -I$(SDL)
LD=gcc
LDFLAGS=-lm -lrt -L$(SDL) -lSDL2 -lSDL2_ttf -lSDL2_gfx -ldl -lpthread
LDFLAGS_D= $(LDFLAGS) #-lmcheck
LDFLAGS_T=-lm -lrt -L. -lt
OBJECTS= \
	point.o graphe.o \
	parse_util.o graphe_parse.o \
	liste_noeud.o dijkstra.o \
	viewport.o \
	graphrep.o window.o app.o
OBJECTS_D= $(subst .o,.do,$(OBJECTS))

VALGRIND=valgrind --leak-check=full -s

.PHONY: help all doc clean_doc clean rendu
.PHONY: test_struct tests runtest_liste_noeud runtest_dijkstra runtests_valgrind

all: test_struct test_liste_noeud test_dijkstra dijkstra

help:
	@echo "Ce Makefile contient les cibles suivantes :"
	@echo "  help                    Affiche cette aide"
	@echo "  all                     Compile tout ce qu'il y a à compiler (cible par défaut)"
	@echo "  dijkstra                Compile le projet dijkstra (l'application principale)"
	@echo "  dijkstra_debug          Compile le projet en mode debug (pour utilisation avec GDB)"
	@echo ""
	@echo "  test_struct             Lance l'outil test_struct pour tester la bonne écriture des fichiers"
	@echo "  test_liste_noeud        Compile les tests unitaires du module liste_noeud"
	@echo "  test_dijkstra           Compile les tests unitaires du module dijkstra"
	@echo "  runtest_liste_noeud     Lance les tests unitaires du module liste_noeud"
	@echo "  runtest_dijkstra        Lance les tests unitaires du module dijkstra"
	@echo "  runtests_valgrind       Lance les tests unitaires des modules liste_noeud et dijkstra avec Valgrind"
	@echo ""
	@echo "  doc                     Génère la documentation du projet"
	@echo ""
	@echo "  clean                   Supprime les artefacts de compilation (.o et exécutables)"
	@echo "  clean_doc               Supprime la documentation générée"
	@echo ""
	@echo "  rendu                   Lance le script de création du rendu"

tests: test_struct test_liste_noeud test_dijkstra

test_struct: liste_noeud.o dijkstra.o
	./test_struct

runtest_liste_noeud: test_liste_noeud
	@echo "================= [Test de liste_noeud] ================="
	./test_liste_noeud

runtest_dijkstra: test_dijkstra
	@echo "================= [ Test de dijkstra  ] ================="
	./test_dijkstra

runtests_valgrind: test_liste_noeud test_dijkstra
	@echo "================= [Test de liste_noeud] ================="
	$(VALGRIND) ./test_liste_noeud
	@echo "================= [ Test de dijkstra  ] ================="
	$(VALGRIND) ./test_dijkstra

dijkstra: main.o $(OBJECTS)
	$(LD) $^ -o $@ $(LDFLAGS)

dijkstra_debug: main.do $(OBJECTS_D)
	$(LD) $^ -o $@ $(LDFLAGS_D)

test_liste_noeud.o: test_liste_noeud.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_dijkstra.o: test_dijkstra.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_liste_noeud: test_liste_noeud.o graphe.do point.do liste_noeud.do
	$(LD) $^ -o $@ $(LDFLAGS_T)

test_dijkstra: test_dijkstra.o graphe.o point.o liste_noeud.o dijkstra.o
	$(LD) $^ -o $@ $(LDFLAGS_T)

main.o: main.c
	$(CC) $(CFLAGS) -c $< -o $@

main.do: main.c
	$(CC) $(CFLAGS_D) -c $< -o $@

%.o: %.c %.h
	$(CC) $(CFLAGS) -c $< -o $@

%.do: %.c %.h
	$(CC) $(CFLAGS_D) -c $< -o $@

rendu: test_struct liste_noeud.h liste_noeud.c dijkstra.h dijkstra.c
	./creer_rendu

doc:
	doxygen

clean_doc:
	-rm -rf doc

clean:
	-rm -f *.o
	-rm -f *.do
	-rm -f dijkstra
	-rm -f dijkstra_debug
	-rm -f test_liste_noeud
	-rm -f test_dijkstra




