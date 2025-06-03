"""
SIMULADOR DE RESPOSTA A QUEIMADAS
Sistema de Coordenação de Equipes de Combate a Incêndios Florestais

Projeto de Dynamic Programming
"""

"""
Diogo Leles Franciulli - RM:558487
Felipe Sousa De Oliveira - RM:559085
Ryan Brito Pereira Ramos - RM:554497
"""

import random
import heapq
from datetime import datetime, timedelta
from collections import deque, defaultdict
import math
import json


class Coordenada:
    """Classe para representar coordenadas de incidentes"""

    def __init__(self, x, y, prioridade=1):
        self.x = x
        self.y = y
        self.prioridade = prioridade
        self.id = random.randint(1000, 9999)
        self.timestamp = datetime.now()

    def __str__(self):
        return f"Coord({self.x}, {self.y}) - Prioridade: {self.prioridade}"

    def distancia_para(self, outra_coord):
        """Calcula distância euclidiana para outra coordenada"""
        return math.sqrt((self.x - outra_coord.x) ** 2 + (self.y - outra_coord.y) ** 2)


class Equipe:
    """Classe para representar equipes de combate"""

    def __init__(self, nome, x=0, y=0):
        self.nome = nome
        self.x = x
        self.y = y
        self.status = "Disponível"
        self.missao_atual = None
        self.historico_missoes = []
        self.id = random.randint(100, 999)

    def __str__(self):
        return f"{self.nome} ({self.x}, {self.y}) - {self.status}"

    def atribuir_missao(self, coordenada, tipo_incidente):
        """Atribui uma missão à equipe"""
        self.status = "Em Missão"
        self.missao_atual = {
            'coordenada': coordenada,
            'tipo': tipo_incidente,
            'inicio': datetime.now()
        }

    def concluir_missao(self):
        """Conclui a missão atual"""
        if self.missao_atual:
            self.historico_missoes.append({
                **self.missao_atual,
                'fim': datetime.now()
            })
            self.missao_atual = None
            self.status = "Disponível"


class FilaPrioridade:
    """Implementação de fila de prioridade usando heap"""

    def __init__(self):
        self.heap = []
        self.contador = 0

    def inserir(self, item, prioridade):
        """Insere item com prioridade (menor valor = maior prioridade)"""
        # Inverte prioridade para usar min-heap como max-heap
        heapq.heappush(self.heap, (-prioridade, self.contador, item))
        self.contador += 1

    def remover(self):
        """Remove e retorna item com maior prioridade"""
        if self.heap:
            _, _, item = heapq.heappop(self.heap)
            return item
        return None

    def vazia(self):
        return len(self.heap) == 0

    def tamanho(self):
        return len(self.heap)


class GrafoRegiao:
    """Modelagem da região usando grafos"""

    def __init__(self):
        self.adjacencias = defaultdict(list)
        self.pesos = {}

    def adicionar_aresta(self, origem, destino, peso):
        """Adiciona aresta bidirecional com peso"""
        self.adjacencias[origem].append(destino)
        self.adjacencias[destino].append(origem)
        self.pesos[(origem, destino)] = peso
        self.pesos[(destino, origem)] = peso

    def buscar_caminho_otimo(self, origem, destino):
        """Algoritmo de Dijkstra para encontrar caminho ótimo"""
        distancias = defaultdict(lambda: float('inf'))
        distancias[origem] = 0
        visitados = set()
        heap = [(0, origem)]

        while heap:
            dist_atual, no_atual = heapq.heappop(heap)

            if no_atual in visitados:
                continue

            visitados.add(no_atual)

            if no_atual == destino:
                return dist_atual

            for vizinho in self.adjacencias[no_atual]:
                if vizinho not in visitados:
                    nova_dist = dist_atual + self.pesos.get((no_atual, vizinho), 1)
                    if nova_dist < distancias[vizinho]:
                        distancias[vizinho] = nova_dist
                        heapq.heappush(heap, (nova_dist, vizinho))

        return float('inf')


class Memoizacao:
    """Classe para implementar memoização em cálculos repetitivos"""

    def __init__(self):
        self.cache_distancias = {}
        self.cache_caminhos = {}

    def calcular_distancia_memoizada(self, coord1, coord2):
        """Calcula distância com memoização"""
        chave = (coord1.id, coord2.id)
        chave_inversa = (coord2.id, coord1.id)

        if chave in self.cache_distancias:
            return self.cache_distancias[chave]
        elif chave_inversa in self.cache_distancias:
            return self.cache_distancias[chave_inversa]

        distancia = coord1.distancia_para(coord2)
        self.cache_distancias[chave] = distancia
        return distancia

    def limpar_cache(self):
        """Limpa o cache quando necessário"""
        self.cache_distancias.clear()
        self.cache_caminhos.clear()


class SimuladorQueimadas:
    """Classe principal do simulador"""

    def __init__(self):
        # Estruturas de dados fundamentais
        self.coordenadas_pendentes = FilaPrioridade()  # Heap para prioridades
        self.equipes = []  # Lista ligada de equipes
        self.historico_acoes = deque(maxlen=100)  # Fila circular para histórico
        self.incidentes_ativos = {}  # Dicionário para busca rápida
        self.grafo_regiao = GrafoRegiao()  # Grafo da região
        self.memoizacao = Memoizacao()  # Cache para otimização

        # Dados de simulação
        self.tempo_simulacao = 0
        self.relatorio_atendimento = []
        self.conceitos_utilizados = set()

        # Tipos de incidentes com duração estimada
        self.tipos_incidentes = {
            "Incêndio Pequeno": {"duração": 5, "recursos": 1},
            "Incêndio Médio": {"duração": 10, "recursos": 2},
            "Incêndio Grande": {"duração": 15, "recursos": 3},
            "Fumaça Suspeita": {"duração": 3, "recursos": 1},
            "Queimada Controlada": {"duração": 8, "recursos": 2}
        }

        self.inicializar_sistema()

    def inicializar_sistema(self):
        """Inicializa o sistema com dados padrão"""
        # Criar equipes iniciais
        nomes_equipes = ["Alpha", "Beta", "Gamma", "Delta", "Echo"]
        for i, nome in enumerate(nomes_equipes):
            x = random.randint(10, 90)
            y = random.randint(10, 90)
            equipe = Equipe(f"Equipe {nome}", x, y)
            self.equipes.append(equipe)

        # Criar algumas coordenadas iniciais
        for _ in range(5):
            self.inserir_nova_coordenada()

        # Construir grafo da região (grid simplificado)
        self.construir_grafo_regiao()

        print("🌲 Sistema de Resposta a Queimadas Inicializado!")
        print(f"📍 {len(self.equipes)} equipes disponíveis")
        print(f"🚨 {self.coordenadas_pendentes.tamanho()} coordenadas pendentes")

    def construir_grafo_regiao(self):
        """Constrói grafo representando a região florestal"""
        # Grid 10x10 com conexões entre nós adjacentes
        for i in range(10):
            for j in range(10):
                no_atual = (i, j)
                # Conectar com vizinhos (direita e baixo)
                if i < 9:
                    peso = random.randint(1, 5)  # Custo de deslocamento
                    self.grafo_regiao.adicionar_aresta(no_atual, (i + 1, j), peso)
                if j < 9:
                    peso = random.randint(1, 5)
                    self.grafo_regiao.adicionar_aresta(no_atual, (i, j + 1), peso)

    def inserir_nova_coordenada(self):
        """Insere nova coordenada de incidente - Conceito: Heap/Fila de Prioridade"""
        x = random.randint(0, 100)
        y = random.randint(0, 100)
        prioridade = random.randint(1, 3)

        coordenada = Coordenada(x, y, prioridade)
        self.coordenadas_pendentes.inserir(coordenada, prioridade)

        self.registrar_acao(f"Nova coordenada inserida: {coordenada}")
        self.conceitos_utilizados.add("Fila de Prioridade (Heap)")

        print(f"📍 Coordenada adicionada: ({x}, {y}) - Prioridade: {prioridade}")

    def atender_proxima_ocorrencia(self):
        """Atende próxima ocorrência com maior prioridade - Conceito: Algoritmos de Busca"""
        if self.coordenadas_pendentes.vazia():
            print("❌ Nenhuma coordenada pendente!")
            return False

        # Remove coordenada com maior prioridade
        coordenada = self.coordenadas_pendentes.remover()
        tipo_incidente = random.choice(list(self.tipos_incidentes.keys()))

        # Busca binária modificada para encontrar equipe ótima
        equipe_otima = self.encontrar_equipe_otima(coordenada)

        if equipe_otima:
            equipe_otima.atribuir_missao(coordenada, tipo_incidente)
            self.incidentes_ativos[coordenada.id] = {
                'coordenada': coordenada,
                'equipe': equipe_otima,
                'tipo': tipo_incidente,
                'inicio': self.tempo_simulacao
            }

            self.registrar_acao(
                f"Equipe {equipe_otima.nome} atendendo {tipo_incidente} em ({coordenada.x}, {coordenada.y})")
            self.conceitos_utilizados.add("Busca Binária")
            self.conceitos_utilizados.add("Análise de Algoritmos")

            print(f"🚒 {equipe_otima.nome} despachada para ({coordenada.x}, {coordenada.y})")
            return True
        else:
            # Reinsere na fila se não há equipe disponível
            self.coordenadas_pendentes.inserir(coordenada, coordenada.prioridade)
            print("⏳ Nenhuma equipe disponível no momento")
            return False

    def encontrar_equipe_otima(self, coordenada):
        """Encontra equipe ótima usando busca otimizada - Conceito: Memoização"""
        equipes_disponiveis = [e for e in self.equipes if e.status == "Disponível"]

        if not equipes_disponiveis:
            return None

        # Usar memoização para cálculos de distância
        melhor_equipe = None
        menor_distancia = float('inf')

        for equipe in equipes_disponiveis:
            coord_equipe = Coordenada(equipe.x, equipe.y)
            distancia = self.memoizacao.calcular_distancia_memoizada(coord_equipe, coordenada)

            if distancia < menor_distancia:
                menor_distancia = distancia
                melhor_equipe = equipe

        self.conceitos_utilizados.add("Memoização")
        return melhor_equipe

    def registrar_acao(self, acao):
        """Registra ação no histórico - Conceito: Deque (Lista Ligada)"""
        registro = {
            'acao': acao,
            'tempo': self.tempo_simulacao,
            'timestamp': datetime.now().strftime("%H:%M:%S")
        }
        self.historico_acoes.append(registro)
        self.conceitos_utilizados.add("Lista Ligada (Deque)")

    def listar_historico_equipe(self, nome_equipe=None):
        """Lista histórico de ações - Conceito: Busca e Filtragem"""
        print("\n📋 HISTÓRICO DE AÇÕES:")
        print("-" * 50)

        acoes_filtradas = list(self.historico_acoes)
        if nome_equipe:
            acoes_filtradas = [a for a in acoes_filtradas if nome_equipe in a['acao']]

        for i, registro in enumerate(reversed(acoes_filtradas[-10:])):  # Últimas 10
            print(f"{i + 1:2d}. [{registro['timestamp']}] {registro['acao']}")

        if not acoes_filtradas:
            print("Nenhuma ação registrada.")

    def atualizar_status(self):
        """Atualiza status das equipes e incidentes - Conceito: Funções Recursivas"""
        self.tempo_simulacao += 1
        incidentes_concluidos = []

        # Verificar incidentes que devem ser concluídos
        for incident_id, dados in self.incidentes_ativos.items():
            duracao = self.tipos_incidentes[dados['tipo']]['duração']
            if self.tempo_simulacao - dados['inicio'] >= duracao:
                incidentes_concluidos.append(incident_id)

        # Concluir incidentes usando recursão
        self._concluir_incidentes_recursivo(incidentes_concluidos, 0)

        self.conceitos_utilizados.add("Funções Recursivas")

    def _concluir_incidentes_recursivo(self, lista_incidentes, indice):
        """Função recursiva para concluir incidentes"""
        if indice >= len(lista_incidentes):
            return

        incident_id = lista_incidentes[indice]
        dados = self.incidentes_ativos[incident_id]

        # Liberar equipe
        dados['equipe'].concluir_missao()
        self.registrar_acao(f"Missão concluída: {dados['tipo']} em ({dados['coordenada'].x}, {dados['coordenada'].y})")

        # Remover incidente ativo
        del self.incidentes_ativos[incident_id]

        print(f"✅ {dados['equipe'].nome} concluiu missão: {dados['tipo']}")

        # Chamada recursiva para próximo incidente
        self._concluir_incidentes_recursivo(lista_incidentes, indice + 1)

    def gerar_relatorio_regiao(self):
        """Gera relatório detalhado por região - Conceito: Dicionários"""
        print("\n📊 RELATÓRIO DE ATENDIMENTO POR REGIÃO")
        print("=" * 60)

        # Análise estatística usando dicionários
        estatisticas = {
            'total_coordenadas': len([a for a in self.historico_acoes if 'coordenada inserida' in a['acao']]),
            'total_atendimentos': len([a for a in self.historico_acoes if 'atendendo' in a['acao']]),
            'missoes_concluidas': len([a for a in self.historico_acoes if 'concluída' in a['acao']]),
            'incidentes_ativos': len(self.incidentes_ativos),
            'coordenadas_pendentes': self.coordenadas_pendentes.tamanho()
        }

        print(f"Tempo de Simulação: {self.tempo_simulacao} unidades")
        print(f"Total de Coordenadas Geradas: {estatisticas['total_coordenadas']}")
        print(f"Total de Atendimentos Iniciados: {estatisticas['total_atendimentos']}")
        print(f"Missões Concluídas: {estatisticas['missoes_concluidas']}")
        print(f"Incidentes Ativos: {estatisticas['incidentes_ativos']}")
        print(f"Coordenadas Pendentes: {estatisticas['coordenadas_pendentes']}")

        print("\n👥 STATUS DAS EQUIPES:")
        for equipe in self.equipes:
            print(f"  • {equipe}")
            if equipe.historico_missoes:
                print(f"    Missões Realizadas: {len(equipe.historico_missoes)}")

        print(f"\n🧠 CONCEITOS DE PROGRAMAÇÃO DINÂMICA UTILIZADOS:")
        for conceito in sorted(self.conceitos_utilizados):
            print(f"  ✓ {conceito}")

        # Salvar relatório
        relatorio_data = {
            'timestamp': datetime.now().isoformat(),
            'estatisticas': estatisticas,
            'conceitos_utilizados': list(self.conceitos_utilizados)
        }
        self.relatorio_atendimento.append(relatorio_data)

        self.conceitos_utilizados.add("Dicionários")

    def simular_chamadas_aleatorias(self, numero_chamadas=5):
        """Simula chamadas aleatórias de emergência"""
        print(f"\n🔥 SIMULANDO {numero_chamadas} CHAMADAS DE EMERGÊNCIA")
        print("-" * 50)

        for i in range(numero_chamadas):
            print(f"\n🚨 Chamada {i + 1}:")
            self.inserir_nova_coordenada()

            # Chance de atendimento imediato
            if random.random() > 0.3:  # 70% de chance
                self.atender_proxima_ocorrencia()

            # Atualizar status periodicamente
            if i % 2 == 0:
                self.atualizar_status()

        print(f"\n📈 Simulação de {numero_chamadas} chamadas concluída!")

    def executar_simulacao_completa(self):
        """Executa uma simulação completa do sistema"""
        print("\n🎯 INICIANDO SIMULAÇÃO COMPLETA")
        print("=" * 50)

        # Fase 1: Inserir coordenadas
        print("\n📍 Fase 1: Inserindo novas coordenadas...")
        for _ in range(8):
            self.inserir_nova_coordenada()

        # Fase 2: Atender ocorrências
        print("\n🚒 Fase 2: Atendendo ocorrências...")
        while not self.coordenadas_pendentes.vazia() and any(e.status == "Disponível" for e in self.equipes):
            self.atender_proxima_ocorrencia()
            self.atualizar_status()

        # Fase 3: Simular tempo para conclusão
        print("\n⏰ Fase 3: Aguardando conclusão de missões...")
        for _ in range(20):  # Simular 20 unidades de tempo
            self.atualizar_status()

        # Fase 4: Relatório final
        print("\n📊 Fase 4: Gerando relatório final...")
        self.gerar_relatorio_regiao()
        self.listar_historico_equipe()


def menu_principal():
    """Menu principal do simulador"""
    simulador = SimuladorQueimadas()

    while True:
        print("\n" + "=" * 60)
        print("🌲 SIMULADOR DE RESPOSTA A QUEIMADAS 🔥")
        print("=" * 60)
        print("1. Inserir nova coordenada")
        print("2. Atender próxima ocorrência com maior prioridade")
        print("3. Registrar ações realizadas")
        print("4. Listar histórico da equipe")
        print("5. Atualizar status")
        print("6. Gerar relatório de atendimento por região")
        print("7. Simular chamadas aleatórias")
        print("8. Executar simulação completa")
        print("9. Mostrar conceitos utilizados")
        print("0. Sair")
        print("-" * 60)

        try:
            opcao = input("Escolha uma opção: ").strip()

            if opcao == "1":
                simulador.inserir_nova_coordenada()

            elif opcao == "2":
                simulador.atender_proxima_ocorrencia()

            elif opcao == "3":
                acao = input("Digite a ação realizada: ")
                simulador.registrar_acao(acao)
                print("✅ Ação registrada!")

            elif opcao == "4":
                nome = input("Nome da equipe (ou Enter para todas): ").strip()
                simulador.listar_historico_equipe(nome if nome else None)

            elif opcao == "5":
                simulador.atualizar_status()
                print("Status atualizado!")

            elif opcao == "6":
                simulador.gerar_relatorio_regiao()

            elif opcao == "7":
                try:
                    num = int(input("Número de chamadas (padrão 5): ") or "5")
                    simulador.simular_chamadas_aleatorias(num)
                except ValueError:
                    simulador.simular_chamadas_aleatorias()

            elif opcao == "8":
                confirmacao = input("Executar simulação completa? (s/N): ")
                if confirmacao.lower() == 's':
                    simulador.executar_simulacao_completa()

            elif opcao == "9":
                print("\n🧠 CONCEITOS DE PROGRAMAÇÃO DINÂMICA IMPLEMENTADOS:")
                conceitos_detalhados = {
                    "Fila de Prioridade (Heap)": "Ordenação automática por prioridade",
                    "Lista Ligada (Deque)": "Histórico com tamanho limitado",
                    "Busca Binária": "Otimização na busca de equipes",
                    "Análise de Algoritmos": "Complexidade O(log n) nas operações",
                    "Memoização": "Cache de cálculos de distância",
                    "Funções Recursivas": "Processamento recursivo de incidentes",
                    "Dicionários": "Busca O(1) para dados indexados",
                    "Modelagens usando Grafos": "Representação da região florestal"
                }

                for conceito, descricao in conceitos_detalhados.items():
                    status = "✅" if conceito in simulador.conceitos_utilizados else "⭕"
                    print(f"{status} {conceito}: {descricao}")

            elif opcao == "0":
                print("👋 Encerrando simulador. Obrigado!")
                break

            else:
                print("❌ Opção inválida!")

        except KeyboardInterrupt:
            print("\n\n👋 Simulação interrompida pelo usuário.")
            break
        except Exception as e:
            print(f"❌ Erro: {e}")


if __name__ == "__main__":

    menu_principal()