#!/usr/bin/env python3
import json
import sys
import os
import re
import subprocess

try:
    from rich.console import Console
    from rich.tree import Tree
    from rich.text import Text
    from rich.panel import Panel
    from rich.table import Table
    from rich.live import Live
    from rich.prompt import Prompt
except ImportError:
    print("Error: This script requires the 'rich' library.")
    print("Please install it with: pip install rich")
    sys.exit(1)

DB_FILE = "sorries.jsonl"

def load_db():
    db = {}
    with open(DB_FILE, "r") as f:
        for line in f:
            if not line.strip(): continue
            obj = json.loads(line)
            if obj.get("i") == "ID": continue
            db[obj["i"]] = obj
    
    # Merge live line numbers from list-sorries.py
    try:
        result = subprocess.run(["./scripts/list-sorries.py"], capture_output=True, text=True)
        for line in result.stdout.splitlines():
            if line.startswith("{"):
                try:
                    live = json.loads(line)
                    # Match by name and file to be safe
                    for node in db.values():
                        if node["s"] == live["s"] and node["f"] == live["f"]:
                            node["l"] = live["l"]
                except: continue
    except:
        pass
        
    return db

def crawl_tex():
    label_to_tex = {}
    for root, _, files in os.walk("tex"):
        for file in files:
            if file.endswith(".tex"):
                path = os.path.join(root, file)
                try:
                    with open(path, "r") as f:
                        for i, line in enumerate(f, 1):
                            match = re.search(r"\\label\{([^}]+)\}", line)
                            if match:
                                label_to_tex[match.group(1)] = (path, i)
                except: continue
    return label_to_tex

def get_style(node):
    if node.get("c") == "done":
        return "green"
    if node.get("r") == 1:
        return "yellow bold"
    return "white dim"

def reachable_status(node):
    r = node.get("r")
    if r == 1:
        return "1"
    if r == 0:
        return "0"
    return "?"

def dependency_counts(db, node):
    upstream = node.get("u", [])
    open_upstream = [uid for uid in upstream if db.get(uid, {}).get("c") != "done"]
    return len(open_upstream), len(upstream)

def dependency_count_text(db, node):
    open_count, total_count = dependency_counts(db, node)
    if total_count == 0:
        return "-"
    return f"{open_count}/{total_count}"

class Outliner:
    def __init__(self, db, tex_map):
        self.db = db
        self.tex_map = tex_map
        self.history = []
        self.direction = "refinement" # "refinement" (Root -> Leaf)
        self.root_mode = "frontier" # "frontier" or "leaves"
        self.show_done = False
        self.current_id = None
        self.console = Console()
        
    def get_roots(self):
        # By default, only show REACHABLE roots
        # A root is either:
        # 1. A node with no downstream dependencies (the ultimate goal)
        # 2. A node that is NOT DONE but all its downstream nodes ARE DONE (the current frontier)
        
        all_nodes = [i for i, n in self.db.items() if n.get("r") == 1]
        
        if not self.show_done:
            # Find nodes that are open
            open_nodes = [i for i in all_nodes if self.db[i].get("c") != "done"]

            if self.root_mode == "leaves":
                # Actionable leaves: open reachable nodes with no open
                # upstream dependencies in the refinement direction.
                leaves = []
                for i in open_nodes:
                    upstream = self.db[i].get("u", [])
                    if all(self.db.get(u, {}).get("c") == "done" for u in upstream):
                        leaves.append(i)
                return leaves
            
            # A node is a "root" in the refinement sense if it is OPEN
            # but all its downstream dependents are either non-existent or DONE.
            roots = []
            for i in open_nodes:
                downstream = self.db[i].get("d", [])
                if not downstream:
                    roots.append(i)
                    continue
                
                # If all downstream nodes are done, this is a frontier root.
                if all(self.db.get(d, {}).get("c") == "done" for d in downstream):
                    roots.append(i)
            
            if not roots and open_nodes:
                # Fallback: if we can't find clear frontiers, show top-level open nodes
                roots = [i for i in open_nodes if not self.db[i].get("d")]
                if not roots: roots = open_nodes[:10]
                
            return roots
        
        if self.root_mode == "leaves":
            return [i for i, n in self.db.items() if not n.get("u") and n.get("r") == 1]

        # If showing done, just return the ultimate goals (nodes with no downstream)
        return [i for i, n in self.db.items() if not n.get("d") and n.get("r") == 1]

    def render_ui(self):
        self.console.clear()
        
        title = f"SORRIES TREE (Refinement Flow: Roots -> Leaves | mode: {self.root_mode})"
        self.console.print(Panel(Text(title, justify="center", style="bold cyan")))

        # Breadcrumbs (Hierarchy Path)
        self.console.print(Text("Path:", style="blue bold"))
        if not self.history and self.current_id is None:
            root_label = "ACTIONABLE LEAVES" if self.root_mode == "leaves" else "SORRY ROOTS"
            self.console.print(Text(f"  {root_label}", style="yellow bold"))
        else:
            for i, hid in enumerate(self.history):
                node = self.db[hid]
                indent = "  " * (i + 1)
                self.console.print(Text(f"{indent}{hid} ", style="blue") + Text(node["s"], style="cyan"))
            
            # Current node
            indent = "  " * (len(self.history) + 1)
            if self.current_id is not None:
                node = self.db[self.current_id]
                self.console.print(Text(f"{indent}{self.current_id} ", style="blue") + Text(node["s"], style="yellow bold"))
        self.console.print("-" * self.console.width)

        # Children
        if self.current_id is not None:
            node = self.db[self.current_id]
            # Refinement: Move toward leaves (u)
            child_ids = node.get("u", [])
            if not self.show_done:
                child_ids = [cid for cid in child_ids if self.db[cid].get("c") != "done"]
            
            # Details
            details = Table.grid(padding=(0, 2))
            details.add_row(Text("Statement:", style="blue"), Text(node["s"], style="yellow"))
            details.add_row(Text("File:", style="blue"), Text(f"{node['f']}:{node.get('l') or '?'}", style="white"))
            details.add_row(Text("Blueprint:", style="blue"), Text(node.get("b") or "None", style="green"))
            details.add_row(Text("Reachable:", style="blue"), Text(reachable_status(node), style="yellow" if node.get("r") == 1 else "white dim"))
            details.add_row(Text("Deps:", style="blue"), Text(dependency_count_text(self.db, node), style="magenta"))
            details.add_row(Text("Effort:", style="blue"), Text(str(node.get("e") or "?"), style="magenta"))
            self.console.print(Panel(details, title="Current Node Details", border_style="blue"))
        else:
            child_ids = self.get_roots()

        if not child_ids:
            msg = "[dim]No remaining open dependencies in this direction.[/dim]" if not self.show_done else "[dim]No further dependencies.[/dim]"
            self.console.print(msg)
        else:
            table = Table(title="Dependencies (Leafward)", box=None, show_header=True, header_style="bold blue")
            table.add_column("ID", style="cyan", width=4)
            table.add_column("r", width=1, justify="center")
            table.add_column("Open/All", style="magenta", width=8, justify="right")
            table.add_column("Effort", style="magenta", width=6, justify="right")
            table.add_column("Statement")
            table.add_column("Status")
            
            for cid in sorted(child_ids):
                cnode = self.db[cid]
                dep_str = dependency_count_text(self.db, cnode)
                effort_str = str(cnode.get("e") or "?")
                
                status = "Done" if cnode.get("c") == "done" else "Open"
                table.add_row(str(cid), reachable_status(cnode), dep_str, effort_str, cnode["s"], status, style=get_style(cnode))
            self.console.print(table)

        # Footer
        footer = Text("\nCommands: ", style="bold")
        footer.append("[ID] dive | ", style="white")
        footer.append("[ID!] jump | ", style="white")
        footer.append("[v] vim lean | ", style="white")
        footer.append("[V] vim tex | ", style="white")
        footer.append("[u] up | ", style="white")
        footer.append("[r] reset | ", style="white")
        next_mode = "leaves" if self.root_mode == "frontier" else "frontier"
        footer.append(f"[m] {next_mode} mode | ", style="white")
        t_label = "hide done" if self.show_done else "show done"
        footer.append(f"[t] {t_label} | ", style="white")
        footer.append("[q] quit", style="white")
        self.console.print(footer)

    def run(self):
        while True:
            self.render_ui()
            choice = input("\n> ").strip()
            
            if choice.lower() == 'q': break
            elif choice.lower() == 'u':
                if self.history: self.current_id = self.history.pop()
                else: self.current_id = None
            elif choice.lower() == 'r':
                self.history = []; self.current_id = None
            elif choice.lower() == 'm':
                self.root_mode = "leaves" if self.root_mode == "frontier" else "frontier"
                self.history = []; self.current_id = None
            elif choice.lower() == 't':
                self.show_done = not self.show_done
            elif choice == 'v' and self.current_id is not None:
                node = self.db[self.current_id]
                line = node.get("l") or 1
                subprocess.run(["vim", f"+{line}", "-c", "normal zz", node["f"]])
            elif choice == 'V' and self.current_id is not None:
                label = self.db[self.current_id].get("b")
                if label in self.tex_map:
                    path, line = self.tex_map[label]
                    subprocess.run(["vim", f"+{line}", "-c", "normal zz", path])
                else:
                    self.console.print(f"[red]No TeX file found for label '{label}'[/red]")
                    input("Press Enter to continue...")
            elif (m := re.match(r"^(\d+)(!)?$", choice)):
                jid = int(m.group(1))
                force = m.group(2) == "!"
                
                if jid not in self.db:
                    self.console.print(f"[red]Error: ID {jid} not found in database.[/red]")
                    input("Press Enter to continue...")
                    continue
                
                # Determine visible IDs
                if self.current_id is not None:
                    visible_ids = self.db[self.current_id].get("u", [])
                else:
                    visible_ids = self.get_roots()
                
                if not self.show_done:
                    visible_ids = [vid for vid in visible_ids if self.db[vid].get("c") != "done"]

                if jid in visible_ids:
                    if self.current_id is not None: self.history.append(self.current_id)
                    self.current_id = jid
                elif force:
                    # Teleport: Reset history to avoid confusing path
                    self.history = []
                    self.current_id = jid
                else:
                    self.console.print(f"[yellow]Warning: ID {jid} is not a visible dependency.[/yellow]")
                    self.console.print(f"To jump directly to this node, type [bold]{jid}![/bold]")
                    input("Press Enter to continue...")


if __name__ == "__main__":
    db = load_db()
    tex_map = crawl_tex()
    Outliner(db, tex_map).run()
