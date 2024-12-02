from selenium import webdriver
from selenium.webdriver.remote.webdriver import WebDriver
from selenium.webdriver.common.action_chains import ActionChains
from selenium.common.exceptions import (StaleElementReferenceException,
                                       TimeoutException,
                                       UnexpectedAlertPresentException,
                                       NoSuchFrameException,
                                       NoAlertPresentException,
                                       WebDriverException,
                                       InvalidElementStateException
                                       )
from bs4 import BeautifulSoup
import hashlib
import adblockparser
import requests
import csv


from urllib.parse import urlparse, urljoin
import json
import pprint
import datetime
import tldextract
import math
import os
import traceback
import random
import re
import time
import itertools
import string

from Functions import *
from extractors.Events import extract_events
from extractors.Forms import extract_forms, parse_form
from extractors.Urls import extract_urls
from extractors.Iframes import extract_iframes
from extractors.Ui_forms import extract_ui_forms

import logging
log_file = os.path.join(os.getcwd(), 'logs', 'crawl-'+str(time.time())+'.log')
logging.basicConfig(filename=log_file, format='%(asctime)s\t%(name)s\t%(levelname)s\t[%(filename)s:%(lineno)d]\t%(message)s', datefmt='%Y-%m-%d:%H:%M:%S', level=logging.DEBUG)
# Turn off all other loggers that we don't care about.
for v in logging.Logger.manager.loggerDict.values():
    v.disabled = True

# This should be the main class for nodes in the graph
# Should contain GET/POST, Form data, cookies,
# events too?
class Request:
    def __init__(self, url, method):
        self.url = url
        # GET / POST
        self.method = method

        # Form data
        # self.forms = []

    def __repr__(self):
        if not self:
            return "NO SELF IN REPR"

        ret = ""
        if not self.method:
            ret = ret + "[NO METHOD?] "
        else:
            ret = ret + "[" + self.method + "] "

        if not self.url:
            ret = ret + "[NO URL?]"
        else:
            ret = ret + self.url

        return ret

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Request):
            return (self.url == other.url and
                    self.method == other.method)
        return False

    def __hash__(self):
        return hash(self.url + self.method)


class Graph:
    def __init__(self):
        self.nodes = []
        self.edges = []
        self.data  = {} # Meta data that can be used for anything

    # Separate node class for storing meta data.
    class Node:
        def __init__(self, value, depth=0):
            self.value = value
            # Meta data for algorithms
            self.visited = False
            self.depth = depth

        def __repr__(self):
            return str(self.value)
        def __eq__(self, other):
            return self.value == other.value
        def __hash__(self):
            return hash(self.value)

    class Edge:
        # Value can be anything
        # For the crawler (type, data) is used,
        # where type = {"get", "form", "event"}
        # and   data = {None, data about form, data about event}
        def __init__(self, n1, n2, value, parent=None):
            self.n1 = n1
            self.n2 = n2
            self.value = value
            self.visited = False
            self.parent = parent
        def __eq__(self, other):
            return self.n1 == other.n1 and self.n2 == other.n2 and self.value == other.value
        def __hash__(self):
            return hash( hash(self.n1) + hash(self.n2) + hash(self.value))
        def __repr__(self):
            return str(self.n1) + " -("+str(self.value)+"["+str(self.visited)+"])-> " + str(self.n2)

    def add(self, value):
        node = self.Node(value)
        if not node in self.nodes:
            self.nodes.append(node)
            return True
        logging.info("failed to add node %s, already added" % str(value))
        return False

    def create_edge(self, v1, v2 , value, parent=None):
        n1   = self.Node(v1)
        n2   = self.Node(v2)
        edge = self.Edge(n1, n2, value, parent)
        return edge

    def connect(self, v1, v2, value, parent=None):
        #print("[connect]",v1,v2,value)
        n1   = self.Node(v1)
        n2   = self.Node(v2)
        edge = self.Edge(n1, n2, value, parent)

        p1 = n1 in self.nodes
        p2 = n2 in self.nodes
        p3 = not (edge in self.edges)
        if (p1 and p2 and p3):
            self.edges.append( edge )
            return True
        logging.warning("Failed to connect edge, %s (%s %s %s)" % (str(value), p1, p2, p3))
        return False

    def visit_node(self, value):
        node = self.Node(value)
        if node in self.nodes:
            target = self.nodes[self.nodes.index(node)]
            target.visited = True
            return True
        return False

    def visit_edge(self, edge):
        if ( edge in self.edges ):
            target = self.edges[self.edges.index(edge)]
            target.visited = True
            return True
        return False

    def unvisit_edge(self, edge):
        if ( edge in self.edges ):
            target = self.edges[self.edges.index(edge)]
            target.visited = False
            return True
        return False

    def get_parents(self, value):
        node = self.Node(value)
        return [edge.n1.value for edge in self.edges if node == edge.n2]

    def __repr__(self):
        res = "---GRAPH---\n"
        for n in self.nodes:
            res += str(n) + " "
        res += "\n"
        for edge in self.edges:
            res += str(edge.n1) + " -("+str(edge.value)+"["+str(edge.visited)+"])-> " + str(edge.n2) + "\n"
        res += "\n---/GRAPH---"
        return res

    # Generates strings that can be pasted into mathematica to draw a graph.
    def toMathematica(self):
        cons = [ ('"' + str(edge.n1) + '" -> "' + str(edge.n2) + '"') for edge in self.edges ]
        data = "{" + ",".join(cons) + "}"

        edge_cons = [ ('("' + str(edge.n1) + '" -> "' + str(edge.n2) + '") -> "' + edge.value.method + "," + str(edge.value.method_data) + '"') for edge in self.edges ]
        edge_data = "{" + ",".join(edge_cons) + "}"

        vertex_labels = 'VertexLabels -> All'
        edge_labels =  'EdgeLabels -> ' + edge_data
        arrow_size = 'EdgeShapeFunction -> GraphElementData["FilledArrow", "ArrowSize" -> 0.005]'
        vertex_size = 'VertexSize -> 0.1'
        image_size = 'ImageSize->Scaled[3]'

        settings = [vertex_labels, edge_labels, arrow_size, vertex_size, image_size]

        res = "Graph["+data+", " + ','.join(settings) + "  ]"

        return res
    
    def edges_from(self, value):
        node = self.Node(value)
        return [edge for edge in self.edges if edge.n1 == node]


class Form:
    def __init__(self):
        self.action = None
        self.method = None
        self.inputs = {}

    # Can we attack this form?
    def attackable(self):
        for input_el in self.inputs:
            if not input_el.itype:
                return  True
            if input_el.itype in ["text", "password", "textarea"]:
                return  True
        return False

    class Element:
        def __init__(self, itype, name, value):
            self.itype =  itype
            self.name  =  name
            self.value =  value
        def __repr__(self):
            return str( (self.itype, self.name, self.value) )
        def __eq__(self, other):
            return (self.itype == other.itype) and (self.name == other.name)
        def __hash__(self):
            return hash(hash(self.itype) + hash(self.name))

    class SubmitElement:
        def __init__(self, itype, name, value, use):
            self.itype =  itype
            self.name  =  name
            self.value =  value
            # If many submit button are available, one must be picked.
            self.use   =  use

        def __repr__(self):
            return str( (self.itype, self.name, self.value, self.use) )
        def __eq__(self, other):
            return ((self.itype == other.itype) and
                   (self.name == other.name) and
                   (self.use == other.use))
        def __hash__(self):
            return hash(hash(self.itype) + hash(self.name) + hash(self.use))

    class RadioElement:
        def __init__(self, itype, name, value):
            self.itype   = itype
            self.name    = name
            self.value   = value
            # Click is used when filling out the form
            self.click   = False
            # User for fuzzing
            self.override_value = ""
        def __repr__(self):
            return str( (self.itype, self.name, self.value, self.override_value) )
        def __eq__(self, other):
            p1 = (self.itype == other.itype)
            p2 = (self.name  == other.name)
            p3 = (self.value == other.value)
            return (p1 and p2 and p3)
        def __hash__(self):
            return hash(hash(self.itype) + hash(self.name) + hash(self.value))

    class SelectElement:
        def __init__(self, itype, name):
            self.itype     = itype
            self.name      = name
            self.options   = []
            self.selected  = None
            self.override_value = ""
        def add_option(self, value):
            self.options.append( value )
        def __repr__(self):
            return str( (self.itype, self.name, self.options, self.selected, self.override_value) )
        def __eq__(self, other):
            return (self.itype == other.itype) and (self.name == other.name)
        def __hash__(self):
            return hash(hash(self.itype) + hash(self.name) )

    class CheckboxElement:
        def __init__(self, itype, name, value, checked):
            self.itype   = itype
            self.name    = name
            self.value   = value
            self.checked = checked
            self.override_value = ""
        def __repr__(self):
            return str( (self.itype, self.name, self.value, self.checked) )
        def __eq__(self, other):
            return (self.itype == other.itype) and (self.name == other.name) and (self.checked == other.checked)
        def __hash__(self):
            return hash(hash(self.itype) + hash(self.name) + hash(self.checked))

    # <select>
    def add_select(self, itype, name):
        new_el = self.SelectElement(itype, name)
        self.inputs[new_el] = new_el
        return self.inputs[new_el]

    # <input>
    def add_input(self, itype, name, value, checked):
        if itype == "radio":
            new_el = self.RadioElement(itype, name, value)
            key    = self.RadioElement(itype, name, value)
        elif itype == "checkbox":
            new_el = self.CheckboxElement(itype, name, value, checked)
            key    = self.CheckboxElement(itype, name, value, None)
        elif itype == "submit":
            new_el = self.SubmitElement(itype, name, value, True)
            key    = self.SubmitElement(itype, name, value, None)
        else:
            new_el = self.Element(itype, name, value)
            key    = self.Element(itype, name, value)

        self.inputs[key] = new_el
        return self.inputs[key]

    # <button>
    def add_button(self, itype, name, value):
        if itype == "submit":
            new_el = self.SubmitElement(itype, name, value, True)
            key    = self.SubmitElement(itype, name, value, None)
        else:
            logging.error("Unknown button " + str((itype,name,value)))
            new_el = self.Element(itype, name, value)
            key    = self.Element(itype, name, value)

        self.inputs[key] = new_el
        return self.inputs[key]

    # <textarea>
    def add_textarea(self, name, value):
        # Textarea functions close enough to a normal text element
        new_el = self.Element("textarea", name, value)
        self.inputs[new_el] = new_el
        return self.inputs[new_el]

    # <iframe>
    def add_iframe_body(self, id):
        new_el = self.Element("iframe", id, "")
        self.inputs[new_el] = new_el
        return self.inputs[new_el]

    def print(self):
        print("[form", self.action, self.method)
        for i in self.inputs:
            print("--", i)
        print("]")

    # For entire Form
    def __repr__(self):
        s  = "Form("+str(len(self.inputs))+", " + str(self.action) + ", " + str(self.method) + ")"
        return s
    def __eq__(self, other):
        return (    self.action == other.action
                and self.method == other.method
                and self.inputs == other.inputs)
    def __hash__(self):
        return hash( hash(self.action) + hash(self.method) + hash(frozenset(self.inputs)) )


# JavaScript events, clicks, onmouse etc.
class Event:
    def __init__(self, fid, event, i, tag, addr, c):
        self.function_id = fid
        self.event = event
        self.id = i
        self.tag = tag
        self.addr = addr
        self.event_class = c
    def __repr__(self):
        s  = "Event("+str(self.event)+", "+self.addr+")"
        return s
    def __eq__(self, other):
        return (self.function_id == other.function_id and
                self.id == other.id and
                self.tag == other.tag and
                self.addr == other.addr)
    def __hash__(self):
        if self.tag == {}:
            logging.warning("Strange tag... %s " % str(self.tag) )
            self.tag = ""
        return hash( hash(self.function_id) +
                     hash(self.id) +
                     hash(self.tag) +
                     hash(self.addr) )


class Iframe:
    def __init__(self, i, src):
        self.id = i
        self.src = src
    def __repr__(self):
        id_str = ""
        src_str = ""
        if self.id:
            id_str = "id=" + str(self.id)
        if self.src:
            src_str = "src=" + str(self.src)
        s  = "Iframe(" + id_str + "," + src_str +")"
        return s
    def __eq__(self, other):
        return (self.id == other.id and
                self.src == other.src
                )
    def __hash__(self):
        return hash( hash(self.id) +
                     hash(self.src)
                      )


class Ui_form:
   def __init__(self, sources, submit):
       self.sources = sources
       self.submit = submit
   def __repr__(self):
       return "Ui_form(" + str(self.sources) + ", " + str(self.submit) + ")"
   def __eq__(self, other):
       self_l = set([ source['xpath'] for source in self.sources ])
       other_l = set([ source['xpath'] for source in other.sources ])
       return self_l == other_l
   def __hash__(self):
       return hash( frozenset([ source['xpath'] for source in self.sources ]) )


class Crawler:
    def __init__(self, driver, url, max_depth=5):
        self.driver = driver
        # Start url
        self.url = url
        self.graph = Graph()

        self.session_id = str(time.time()) + "-" + str(random.randint(1,10000000))

        # Used to track injections. Each injection will have unique key.
        self.attack_lookup_table = {}

        # input / output graph
        self.io_graph = {}

        # Optimization to do multiple events in a row without
        # page reloads.
        self.events_in_row = 0
        self.max_events_in_row = 5

        # Start with gets
        self.early_gets = 0
        self.max_early_gets = 50

        # Dont attack same form too many times
        # hash -> number of attacks
        self.attacked_forms = {}

        # Dont submit same form too many times
        self.done_form = {}
        self.max_done_form = 5

        logging.info("Init crawl on " + url)

        # Extract JS codes
        self.hash_set = set()
        self.filters = {}
        self.load_js = 0
        self.max_depth = max_depth

    # 1) Start
    def start(self, debug_mode=False):
        self.root_req = Request("ROOTREQ", "get")
        req = Request(self.url, "get")
        self.graph.add(self.root_req)
        self.graph.add(req)
        self.graph.connect(self.root_req, req, CrawlEdge("get", None, None) )
        self.debug_mode = debug_mode

        # Path deconstruction
        # TODO arg for this
        if not debug_mode:
            purl = urlparse(self.url)
            if purl.path :
                path_builder = ""
                for d in purl.path.split("/")[:-1]:
                    if d:
                        path_builder += d + "/"
                        tmp_purl = purl._replace(path=path_builder)
                        req = Request(tmp_purl.geturl(), "get")
                        self.graph.add(req)
                        self.graph.connect(self.root_req, req, CrawlEdge("get", None, None) )

        self.graph.data['urls'] = {}
        self.graph.data['form_urls'] = {}
        open("run.flag", "w+").write("1")
        open("queue.txt", "w+").write("")
        open("command.txt", "w+").write("")

        random.seed( 6 ) # chosen by fair dice roll

        still_work = True
        while still_work:
            print("-"*50)
            new_edges = len([edge for edge in self.graph.edges if edge.visited == False])
            print("Edges left: %s" % str(new_edges))
            try:
                #f = open("graph.txt", "w")
                #f.write( self.graph.toMathematica() )

                if "0" in open("run.flag", "r").read():
                    logging.info("Run set to 0, stop crawling")
                    break
                if "2" in open("run.flag", "r").read():
                    logging.info("Run set to 2, pause crawling")
                    input("Crawler paused, press enter to continue")
                    open("run.flag", "w+").write("3")

                n_gets = 0
                n_forms = 0
                n_events = 0
                for edge in self.graph.edges:
                    if edge.visited == False:
                        if edge.value.method == "get":
                            n_gets += 1
                        elif edge.value.method == "form":
                            n_forms += 1
                        elif edge.value.method == "event":
                            n_events += 1
                print()
                print("----------------------")
                print("GETS    | FROMS  | EVENTS ")
                print(str(n_gets).ljust(7), "|", str(n_forms).ljust(6), "|", n_events)
                print("----------------------")

                try:
                    still_work = self.rec_crawl()
                except Exception as e:
                    still_work = n_gets + n_forms + n_events
                    print(e)
                    print(traceback.format_exc())
                    logging.error(e)
                    logging.error("Top level error while crawling")
                #input("Enter to continue")
            except KeyboardInterrupt:
                print("CTRL-C, abort mission")
                #print(self.graph.toMathematica())
                break

        print("Done crawling, ready to attack!")
        # self.attack()

    # 2) Fined Crawl
    # Handle priority
    def next_unvisited_edge(self, driver, graph):
        user_url = open("queue.txt", "r").read()
        if user_url:
            print("User supplied url: ", user_url)
            logging.info("Adding user from URLs " + user_url)

            req = Request(user_url,"get")
            current_cookies = driver.get_cookies()
            new_edge = graph.create_edge(self.root_req, req, CrawlEdge(req.method, None, current_cookies), graph.data['prev_edge'] )
            graph.add(req)
            graph.connect(self.root_req, req, CrawlEdge(req.method, None, current_cookies), graph.data['prev_edge'] )

            print(new_edge)

            open("queue.txt", "w+").write("")
            open("run.flag", "w+").write("3")

            successful = follow_edge(driver, graph, new_edge)
            if successful:
                return new_edge
            else:
                logging.error("Could not load URL from user " + str(new_edge) )

        # Always handle the iframes
        list_to_use = [edge for edge in graph.edges if edge.value.method == "iframe" and edge.visited == False]
        if list_to_use:
            print("Following iframe edge")

        # Start the crawl by focusing more on GETs
        if not self.debug_mode:
            if self.early_gets < self.max_early_gets:
                print("Looking for EARLY gets")
                print(self.early_gets, "/", self.max_early_gets)
                list_to_use = [edge for edge in graph.edges if edge.value.method == "get" and edge.visited == False]
                list_to_use = linkrank(list_to_use, graph.data['urls'])
                # list_to_use = new_files(list_to_use, graph.data['urls'])
                # list_to_use = reversed( list_to_use )
                if list_to_use:
                    self.early_gets += 1
                else:
                    print("No get, trying something else")
            if self.early_gets == self.max_early_gets:
                print("RESET")
                for edge in graph.edges:
                    graph.unvisit_edge(edge)
                graph.data['urls'] = {}
                graph.data['form_urls'] = {}
                self.early_gets += 1

        if not list_to_use:
            random_int = random.randint(0,100)
            if not list_to_use:
                if random_int >= 0 and random_int < 50:
                    print("Looking for form")
                    list_to_use = [edge for edge in graph.edges if edge.value.method == "form" and edge.visited == False]
                elif random_int >= 50 and random_int < 80:
                    print("Looking for get")
                    list_to_use = [edge for edge in graph.edges if edge.value.method == "get" and edge.visited == False]
                    list_to_use = linkrank(list_to_use, graph.data['urls'])
                else:
                    print("Looking for event")
                    print("--Clicks")
                    list_to_use = [edge for edge in graph.edges if edge.value.method == "event" and ("click" in edge.value.method_data.event) and edge.visited == False]
                    if not list_to_use:
                        print("--No clicks found, check all")
                        list_to_use = [edge for edge in graph.edges if edge.value.method == "event" and edge.visited == False]

        # Try fallback to GET
        if not list_to_use:
            logging.warning("Falling back to GET")
            list_to_use = [edge for edge in graph.edges if edge.value.method == "get" and edge.visited == False]
            list_to_use = linkrank(list_to_use, graph.data['urls'])

        # for edge in graph.edges:
        for edge in list_to_use:
            if edge.visited == False:
                if not check_edge(driver, graph, edge):
                    logging.warning("Check_edge failed for " + str(edge))
                    edge.visited = True
                else:
                    successful = follow_edge(driver, graph, edge)
                    if successful:
                        return edge

        # Final fallback to any edge
        for edge in graph.edges:
            if edge.visited == False:
                if not check_edge(driver, graph, edge):
                    logging.warning("Check_edge failed for " + str(edge))
                    edge.visited = True
                else:
                    successful = follow_edge(driver, graph, edge)
                    if successful:
                        return edge

        # Check if we are still in early explore mode
        if self.early_gets < self.max_early_gets:
            # Turn off early search
            self.early_gets = self.max_early_gets
            return self.next_unvisited_edge(driver, graph)

        return None

    def load_page(self, driver, graph):
        request = None
        edge = self.next_unvisited_edge(driver, graph)
        if not edge:
            return None

        # Update last visited edge
        graph.data['prev_edge'] = edge

        request = edge.n2.value

        logging.info("Current url: " + driver.current_url)
        logging.info("Crawl (edge): " +  str(edge) )
        print("Crawl (edge): " +  str(edge) )

        return (edge,request)
  
    # Actually not recursive (TODO change name)
    def rec_crawl(self, current_edge=None, current_node=None, depth=0, trigger_sequence=None):

        if depth > self.max_depth:
            return  # 더 이상 탐색하지 않고 종료

        driver = self.driver
        graph = self.graph

        if current_node is None:
            todo = self.load_page(driver, graph)
            if not todo:
                print("Done crawling")
                print(graph)
                pprint.pprint(self.io_graph)

                for tracker in self.io_graph:
                    if self.io_graph[tracker]['reflected']:
                        print("EDGE FROM ", self.io_graph[tracker]['injected'], "to", self.io_graph[tracker]['reflected'])

                f = open("graph_mathematica.txt", "w")
                f.write( self.graph.toMathematica() )

                return False

            (edge, request) = todo
            graph.visit_node(request)
            graph.visit_edge(edge)
            current_node = request
            sequence = []
        else:
            edge = current_edge
            request = current_node
            sequence = trigger_sequence.copy()
        
        sequence.append(str(current_node))
        print("Exploring node: " + " -> ".join(sequence) + f" at depth {depth}")

        # (almost) Never GET twice (optimization)
        if edge.value.method == "get":
            for e in graph.edges:
                if (edge.n2 == e.n2) and (edge != e) and (e.value.method == "get"):
                    #print("Fake visit", e)
                    graph.visit_edge(e)

        # Wait if needed
        try:
            wait_json = driver.execute_script("return JSON.stringify(need_to_wait)")
            wait = json.loads(wait_json)
            if wait:
                time.sleep(1)
        except UnexpectedAlertPresentException:
            logging.warning("Alert detected")
            alert = driver.switch_to_alert()
            alert.dismiss()

            # Check if double check is needed...
            try:
                wait_json = driver.execute_script("return JSON.stringify(need_to_wait)")
                wait = json.loads(wait_json)
                if wait:
                    time.sleep(1)
            except:
                logging.warning("Inner wait error for need_to_wait")
        except:
            logging.warning("No need_to_wait")

        # Timeouts
        try:
            resps = driver.execute_script("return JSON.stringify(timeouts)")
            todo = json.loads(resps)
            for t in todo:
                try:
                    if t['function_name']:
                        driver.execute_script(t['function_name'] + "()")
                except:
                    logging.warning("Could not execute javascript function in timeout " + str(t))
        except:
            logging.warning("No timeouts from stringify")

        early_state = self.early_gets < self.max_early_gets
        login_form = find_login_form(driver, graph, early_state)

        if login_form:
            logging.info("Found login form")
            print("We want to test edge: ", edge)
            new_form = set_form_values(set([login_form])).pop()
            try:
                print("Logging in")
                form_fill(driver, new_form)
            except:
                logging.warning("Failed to login to potiential login form")

        # Extract urls, forms, elements, iframe etc
        reqs = extract_urls(driver)
        forms = extract_forms(driver)
        forms = set_form_values(forms)
        ui_forms = extract_ui_forms(driver)
        events = extract_events(driver)
        iframes = extract_iframes(driver)

        # Check if we need to wait for asynch
        try:
            wait_json = driver.execute_script("return JSON.stringify(need_to_wait)")
        except UnexpectedAlertPresentException:
            logging.warning("Alert detected")
            alert = driver.switch_to_alert()
            alert.dismiss()
        wait_json = driver.execute_script("return JSON.stringify(need_to_wait)")
        wait = json.loads(wait_json)
        if wait:
            time.sleep(1)

        # Add findings to the graph
        current_cookies = driver.get_cookies()

        logging.info("Adding requests from URLs")
        for req in reqs:
            logging.info("from URLs %s " % str(req))
            new_edge = graph.create_edge(request, req, CrawlEdge(req.method, None, current_cookies), edge )
            if allow_edge(graph, new_edge):
                graph.add(req)
                graph.connect(request, req, CrawlEdge(req.method, None, current_cookies), edge )
            else:
                logging.info("Not allowed to add edge: %s" % new_edge)

        logging.info("Adding requests from froms")
        for form in forms:
            req = Request(form.action, form.method)
            logging.info("from forms %s " % str(req))
            new_edge = graph.create_edge( request, req, CrawlEdge("form", form, current_cookies), edge )
            if allow_edge(graph, new_edge):
                graph.add(req)
                graph.connect(request, req, CrawlEdge("form", form, current_cookies), edge )
            else:
                logging.info("Not allowed to add edge: %s" % new_edge)

        logging.info("Adding requests from events")
        for event in events:
            req = Request(request.url, "event")
            logging.info("from events %s " % str(req))

            new_edge = graph.create_edge( request, req, CrawlEdge("event", event, current_cookies), edge )
            if allow_edge(graph, new_edge):
                graph.add(req)
                graph.connect(request, req, CrawlEdge("event", event, current_cookies), edge )
            else:
                logging.info("Not allowed to add edge: %s" % new_edge)

        logging.info("Adding requests from iframes")
        for iframe in iframes:
            req = Request(iframe.src, "iframe")
            logging.info("from iframes %s " % str(req))

            new_edge = graph.create_edge( request, req, CrawlEdge("iframe", iframe, current_cookies), edge )
            if allow_edge(graph, new_edge):
                graph.add(req)
                graph.connect(request, req, CrawlEdge("iframe", iframe, current_cookies), edge )
            else:
                logging.info("Not allowed to add edge: %s" % new_edge)

        logging.info("Adding requests from ui_forms")
        for ui_form in ui_forms:
            req = Request(driver.current_url, "ui_form")
            logging.info("from ui_forms %s " % str(req))

            new_edge = graph.create_edge( request, req, CrawlEdge("ui_form", ui_form, current_cookies), edge )
            if allow_edge(graph, new_edge):
                graph.add(req)
                graph.connect(request, req, CrawlEdge("ui_form", ui_form, current_cookies), edge )
            else:
                logging.info("Not allowed to add edge: %s" % new_edge)

        # Try to clean up alerts
        try:
            alert = driver.switch_to_alert()
            alert.dismiss()
        except NoAlertPresentException:
            pass

        # Check for successful attacks
        # time.sleep(0.1)
        # self.inspect_attack(edge)
        # self.inspect_tracker(edge)

        if "3" in open("run.flag", "r").read():
            logging.info("Run set to 3, pause each step")
            input("Crawler in stepping mode, press enter to continue. EDIT run.flag to run")

        # Check command
        found_command = False
        if "get_graph" in open("command.txt", "r").read():
            f = open("graph.txt", "w+")
            f.write(str(self.graph))
            f.close()
            found_command = True
        # Clear commad
        if found_command:
            open("command.txt", "w+").write("")

        self.extract_JS(sequence)
        for edge in graph.edges_from(current_node):
            next_node = edge.n2.value
            if not graph.visit_node(next_node):
                logging.info(f"Recursively visiting: {next_node}")
            self.rec_crawl(new_edge, next_node, depth + 1, sequence)
        logging.info(f"Returning from node: {current_node} at depth {depth}")

        return True

    # 3) Extract JS
    def hash_content(self, content):
        return hashlib.sha256(content.encode('utf-8')).hexdigest()

    def get_filter_lists(self, filter_lists_path):
        os.makedirs(filter_lists_path)
        
        filter_lists = {
            'EasyList': 'https://easylist.to/easylist/easylist.txt',
            'EasyPrivacy': 'https://easylist.to/easylist/easyprivacy.txt',
            'Fanboy\'s Annoyance List': 'https://easylist.to/easylist/fanboy-annoyance.txt',
            'Peter Lowe\'s List': 'https://pgl.yoyo.org/adservers/serverlist.php?hostformat=adblockplus&mimetype=plaintext',
        }
        for name, url in filter_lists.items():
            filter_list_path = os.path.join(filter_lists_path, f'{name}.txt')
            
            content = requests.get(url).content
            with open(filter_list_path, 'wb') as f:
                f.write(content)
            
            with open(filter_list_path, 'r') as f:
                raw_rules = f.read().splitlines()
            
            filter_lists[name] = adblockparser.AdblockRules(raw_rules)
        
        self.filters = filter_lists

    def is_tracker(self, script_url):
        count = sum(self.filters[name].should_block(script_url) for name in self.filters)
        if count >= 2:
            return True
        return False

    def save_to_csv(self, csv_file_path, root_url, file_name, hash, trigger_sequence, label):
        if not os.path.exists(csv_file_path):
            with open(csv_file_path, mode="w", encoding="utf-8", newline="") as csvfile:
                writer = csv.writer(csvfile)
                writer.writerow(["Root URL", "File Name", "Hashcode", "Trigger Sequence", "Label"])

        with open(csv_file_path, mode="a", encoding="utf-8", newline="") as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow([root_url, file_name, hash, " -> ".join(trigger_sequence), label])

    def save_file(self, file_path, content):
        with open(file_path, 'a', encoding='utf-8') as f:
            f.write(content)

    def extract_JS(self, trigger_sequence):
        OUTPUT_DIR = "./js_output"
        driver = self.driver
        soup = BeautifulSoup(driver.page_source, 'html.parser')

        external_js_urls = [tag['src'] for tag in soup.find_all('script', src=True)]
        for script_url in external_js_urls:
            full_script_url = urljoin(driver.current_url, script_url)
            try:
                response = requests.get(full_script_url)
                if response.status_code == 200:
                    script_content = response.text
                else:
                    print(f"Failed to fetch script: {full_script_url}, status code: {response.status_code}")
                    continue
            except requests.RequestException as e:
                print(f"Error fetching script: {full_script_url}, error: {e}")
                continue

            content_hash = self.hash_content(script_content)
            if content_hash not in self.hash_set:
                self.hash_set.add(content_hash)
                os.makedirs((os.path.join(OUTPUT_DIR, content_hash)))
                self.save_file(os.path.join(os.path.join(OUTPUT_DIR, content_hash), "code"), script_content)
                if self.is_tracker(script_url):
                    self.save_file(os.path.join(os.path.join(OUTPUT_DIR, content_hash), "label"), "1")
                    self.save_to_csv(os.path.join(OUTPUT_DIR, "script_logs.csv"), driver.current_url, full_script_url, content_hash, trigger_sequence, "1")
                else:
                    self.save_file(os.path.join(os.path.join(OUTPUT_DIR, content_hash), "label"), "0")
                    self.save_to_csv(os.path.join(OUTPUT_DIR, "script_logs.csv"), driver.current_url, full_script_url, content_hash, trigger_sequence, "0")

        # inline의 경우 labeling을 어떻게 하는거지? 그냥 정상코드로 인식해야하나..?
        inline_js = [tag.text for tag in soup.find_all('script') if tag.text.strip()]
        for script in inline_js:
            content_hash = self.hash_content(script)
            if content_hash not in self.hash_set:
                self.hash_set.add(content_hash)
                os.makedirs((os.path.join(OUTPUT_DIR, content_hash))) 
                self.save_file(os.path.join(os.path.join(OUTPUT_DIR, content_hash), "code"), script)
                self.save_file(os.path.join(os.path.join(OUTPUT_DIR, content_hash), "label"), "0")
                self.save_to_csv(os.path.join(OUTPUT_DIR, "script_logs.csv"), driver.current_url, f"url_{self.load_js}.js", content_hash, trigger_sequence, "0")
                self.load_js += 1


# Edge with specific crawling info, cookies, type of request etc.
class CrawlEdge:
    def __init__(self, method, method_data, cookies):
        self.method = method
        self.method_data = method_data
        self.cookies = cookies
    def __repr__(self):
        return str(self.method) + " " + str(self.method_data)
    # Cookies are not considered for equality.
    def __eq__(self, other):
        return (self.method == other.method and self.method_data == other.method_data)
    def __hash__(self):
        return hash( hash(self.method) + hash(self.method_data) )

