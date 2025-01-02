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

from bs4 import BeautifulSoup
import hashlib
import adblockparser
import requests
import csv
import matplotlib.pyplot as plt
import networkx as nx

from Functions import *
from extractors.Events import extract_events
from extractors.Forms import extract_forms, parse_form
from extractors.Urls import extract_urls
from extractors.Iframes import extract_iframes
from extractors.Ui_forms import extract_ui_forms

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
        def __init__(self, value):
            self.value = value
            # Meta data for algorithms
            self.visited = False
            self.number_of_js = 0

        def update_js_info(self, num):
            self.number_of_js = num
            print(f"{num} of JS are loaded.")
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
            self.depth = parent.depth + 1 if parent else 0
            self.cnt_gets = parent.cnt_gets + 1 if parent and value.method == "get" else 0
            self.cnt_forms = parent.cnt_forms + 1 if parent and value.method == "form" else 0
            self.cnt_events = parent.cnt_events + 1 if parent and value.method == "event" else 0
            
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
        #print(p1,p2,p3)
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
        s  = "Event("+str(self.event)+", " + self.addr + ")"
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