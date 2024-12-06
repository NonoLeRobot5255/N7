from manim import *

class CityGraph(Scene):
    def construct(self):
        white_theme = True
        if white_theme:
            self.camera.background_color = "#F5F5DC"  # Beige

        city_positions = {
            "Paris": [-2, 1, 0],
            "Bruxelles": [-3, 3, 0],
            "Francfort": [2, 0, 0],
            "Zurich": [-5, -2, 0],
            "Milan": [3, 3, 0]
        }

        edges = [
            ("Paris", "Bruxelles", 320),
            ("Paris", "Francfort", 479), #1
            ("Paris", "Zurich", 489),
            ("Paris", "Milan", 850), #3
            ("Bruxelles", "Francfort", 404), #4
            ("Bruxelles", "Zurich", 663),
            ("Bruxelles", "Milan", 819), #6
            ("Francfort", "Zurich", 305), #7
            ("Francfort", "Milan", 518),
            ("Zurich", "Milan", 279) #9
        ]

        graph = Graph(
            vertices=list(city_positions.keys()),
            edges=[(e[0], e[1]) for e in edges],
            layout=city_positions,
            edge_config={(e[0], e[1]): {"stroke_width": 3} for e in edges},
        )
        labels = VGroup()
        for name in city_positions.keys():
            label = MathTex(name).scale(0.5)
            if name == 'Francfort':
                label.next_to(graph.vertices.get(name), 12*RIGHT+4*DOWN, buff=0.1)
            elif name == 'Paris':
                label.next_to(graph.vertices.get(name), 1*RIGHT+2.5*DOWN, buff=0.1)
            else:
                label.next_to(graph.vertices.get(name), 0.5*DOWN+1*RIGHT, buff=0.1)
            if white_theme:
                label.set_color(BLACK)
            labels.add(label)
        # Déplacer le graphe au centre de la scène
        if white_theme:
            for v in graph.vertices.keys():
                graph.vertices.get(v).set_color('#d2b48c')
        graph.move_to(ORIGIN)
        graph.set_z_index(2)
        lines = VGroup()
        distances = [e[2] for e in edges]
        dists = VGroup()
        for e in graph.edges:
            if white_theme:
                line = Line(graph[e[0]].get_center(), graph[e[1]].get_center(), stroke_width=2, color='#8b4513')
            else:
                line = Line(graph[e[0]].get_center(), graph[e[1]].get_center(), stroke_width=2)
            lines.add(line)

        for i in range(len(lines)):
            dist = MathTex(distances[i]).scale(0.5)
            if white_theme:
                dist.set_color(BLACK)
            else:
                dist.set_color(BLUE_A)
            dist.next_to(lines[i].get_center(),RIGHT,buff=0.1)
            dist.set_z_index(3)
            dists.add(dist)
        dists[3].shift(0.25*UP)
        dists[6].shift(0.25*UP)
        dists[1].shift(0.25*DOWN)
        dists[7].shift(0.25*DOWN)
        dists[7].shift(0.1*DOWN + 0.1*LEFT)
        dists[9].shift(0.2*DOWN + 0.1*LEFT)
        # Créer une liste d'animations Create pour toutes les lignes
        create_animations = [Create(line) for line in lines]

        # Ajouter le graphe à la scène
        # Créer le graphe avec des animations
        # Ajouter le graphe et les étiquettes à la scène avec des animations
        self.play(
            LaggedStart(*[
                Succession(
                    FadeIn(graph[v]),
                    FadeIn(labels[i])
                ) for i, v in enumerate(graph.vertices)
            ], lag_ratio=0.04)
        )

        # Jouer toutes les animations Create simultanément
        self.play(AnimationGroup(*create_animations, lag_ratio=0, run_time=4, rate_func=rate_functions.smooth),Write(dists))
        self.wait()

        # Implementing Kruskal's algorithm visualization
        parent = {v: v for v in city_positions.keys()}

        def find(v):
            if parent[v] != v:
                parent[v] = find(parent[v])
            return parent[v]

        def union(v1, v2):
            root1 = find(v1)
            root2 = find(v2)
            if root1 != root2:
                parent[root2] = root1

        edges_sorted = sorted(edges, key=lambda e: e[2])
        mst_edges = []
        first = True
        used_vertices = []
        for edge in edges_sorted:
            v1, v2, weight = edge
            if first:
                graph.vertices[v1].set_color(GREEN)
                first = False
            if find(v1) != find(v2):
                union(v1, v2)
                mst_edges.append(edge)
                index = edges.index(edge)
                if v1 in used_vertices:
                    graph.vertices[v1].set_color(GREEN)
                    self.play(Indicate(graph.vertices[v1], scale_factor=1.5, color=RED))
                else:
                    graph.vertices[v2].set_color(GREEN)
                    self.play(Indicate(graph.vertices[v2], scale_factor=1.5, color=RED))
                self.wait(0.25)
                if v1 in used_vertices:
                    graph.vertices[v2].set_color(GREEN)
                    anim = Indicate(graph.vertices[v2], scale_factor=1.5, color=GREEN)
                else:
                    graph.vertices[v1].set_color(GREEN)
                    anim = Indicate(graph.vertices[v1], scale_factor=1.5, color=GREEN)
                self.play(graph.edges[v1, v2].set_z_index(1).animate.set_color("#4682B4").set_stroke(width=6),
                          FadeOut(dists[index]),anim)
                self.wait(0.5)
                used_vertices.append(v1),
                used_vertices.append(v2),
        self.wait(2)

#manim -p -ql --resolution 1920,1080 Dani1.py
