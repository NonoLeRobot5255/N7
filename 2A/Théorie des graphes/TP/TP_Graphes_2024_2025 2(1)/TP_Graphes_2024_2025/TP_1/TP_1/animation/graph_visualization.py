from manim import *
import scipy.io as sio
import numpy as np

config.tex_template = TexTemplate()
config.tex_template.add_to_preamble(r"\usepackage[utf8]{inputenc}")
config.tex_template.add_to_preamble(r"\usepackage[T1]{fontenc}")


def normalize_array(arr):
    # Normaliser le tableau pour que ses valeurs soient comprises entre 0 et 1
    norm_arr = (arr - np.min(arr)) / (np.max(arr) - np.min(arr))
    return norm_arr


class GraphVisualization(Scene):

    def construct(self):

        white_theme = True
        if white_theme:
            self.camera.background_color = "#F5F5DC"  # Beige

        # Charger les données
        A = sio.loadmat('donnees/temp/adj_matrix.mat')['adj']
        pos = sio.loadmat('donnees/constant/position.mat')['pos']
        posNormalized = normalize_array(pos)
        n = len(posNormalized)
        posNormalizedSpace = [[posNormalized[i][0] * 14, posNormalized[i][1] * 8, 0] for i in range(n)]
        nodenames = sio.loadmat('donnees/constant/nodename.mat')['cities'][0]
        nodenames = [name[0] for name in nodenames]

        # Convertir la matrice d'adjacence en un dictionnaire de connexions
        edges = [(i + 1, j + 1) for i in range(n) for j in range(n) if (A[i, j] != 0 and i != j)]
        vertices = [i + 1 for i in range(n)]
        lt = {i + 1: posNormalizedSpace[i] for i in range(n)}
        graph = Graph(vertices, edges, layout=lt)
        if white_theme:
            for v in graph.vertices.keys():
                graph.vertices.get(v).set_color('#d2b48c')
        graph.move_to(ORIGIN)
        graph.set_z_index(2)
        lines = VGroup()
        for e in graph.edges:
            if white_theme:
                line = Line(graph[e[0]].get_center(), graph[e[1]].get_center(), stroke_width=2, color='#8b4513')
            else:
                line = Line(graph[e[0]].get_center(), graph[e[1]].get_center(), stroke_width=2)
            lines.add(line)
        lines.set_z_index(1)
        # Créer les étiquettes
        labels = VGroup()
        for i, name in enumerate(nodenames):
            label = MathTex(name).scale(0.5)
            if name in ["Dublin", "Amsterdam", "Oslo", "Minsk"]:
                label.next_to(graph[i+1], UP, buff=0.1)
            elif name in ["London", "Prague", "Berlin", "Copenhagen"]:
                label.next_to(graph[i+1], LEFT, buff=0.1)
            elif name in ["Brussels", "Vienna"]:
                label.next_to(graph[i+1], RIGHT, buff=0.1)
            else:
                label.next_to(graph[i+1], DOWN, buff=0.1)
            if white_theme:
                label.set_color(BLACK)
            labels.add(label)
        labels.set_z_index(3)
        self.play(
            LaggedStart(*[
                Succession(
                    FadeIn(graph[v]),
                    FadeIn(labels[i])
                ) for i, v in enumerate(graph.vertices)
            ], lag_ratio=0.02)
        )
        self.play(
            AnimationGroup(*[Create(line) for line in lines], lag_ratio=0, run_time=4, rate_func=rate_functions.smooth))
        self.wait()
